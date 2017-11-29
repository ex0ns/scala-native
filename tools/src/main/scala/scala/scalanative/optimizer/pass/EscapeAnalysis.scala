package scala.scalanative
package optimizer
package pass


import scala.collection.mutable
import scala.scalanative.nir.Inst.{Jump, Label, Let}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy._
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.ClassRef

class EscapeAnalysis(config: tools.Config)(implicit top: Top) extends Pass {
  import EscapeAnalysis._

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val classes = new mutable.HashSet[Local]()

    insts foreach {
      case inst @ Let(name, Op.Classalloc(_)) =>
        classes.add(name)
      case  Let(_, op : Op.Store) =>
        val vals = new AllVals()
        vals.onOp(op)
        classes --= vals.vals
      case Let(_, op: Op.Copy) =>
        val vals = new AllVals()
        vals.onOp(op)
        classes --= vals.vals
      case Let(_, op: Op.Call) =>
        val vals = new AllVals()
        vals.onOp(op)
        classes --= vals.vals
      case Jump(next @ Next.Label(_, args)) =>
        val vals = new AllVals()
        vals.onNext(next)
        classes --= vals.vals
      case _ =>
    }

    val buf = new nir.Buffer()

    insts foreach {
      case inst @ Let(name, Op.Classalloc(ClassRef(node))) if classes.contains(name) =>
        val struct = node.layout.struct
        val size = node.layout.size
        val rtti = node.rtti

        val dst = Val.Local(name, Type.Ptr)

        buf ++= Seq(
          Let(name, Op.Stackalloc(struct, nir.Val.None)),
          Let(fresh(),
            Op.Call(memsetSig,
                    memset,
                    Seq(
                      dst,
                      Val.Byte(0),
                      Val.Long(size),
                      Val.Int(1), // Align
                      Val.Bool(false) // Volatile
          ), Next.None)),
          Let(fresh(), Op.Store(rtti.struct, dst, rtti.value)) //@TODO Find why rtti does not work
        )
      case inst @_ => buf += inst
    }

    buf.toSeq
  }
}


object EscapeAnalysis extends PassCompanion {

  override val depends = Seq()

  val memsetSig = Type.Function(Seq(Type.Ptr, Type.Byte, Type.Long, Type.Int, Type.Bool), Type.Void)
  val memSetName = Global.Top("llvm.memset.p0i8.i64")
  val memset     = Val.Global(memSetName, memsetSig)

  override val injects =
    Seq(Defn.Declare(Attrs.None, memSetName, memsetSig))

  override def apply(config: tools.Config, top: Top) =
    new EscapeAnalysis(config)(top)
}

private class AllVals extends Pass {
  val vals : mutable.Set[Local] = mutable.Set[Local]()

  override def onVal(value: Val): Val = value match {
      case Val.Local(local, _) =>
        vals.add(local)
        value
      case _ => super.onVal(value)

  }
}