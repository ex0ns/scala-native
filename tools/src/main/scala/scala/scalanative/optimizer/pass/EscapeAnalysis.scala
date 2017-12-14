package scala.scalanative
package optimizer
package pass


import scala.collection.mutable
import scala.scalanative.nir.Inst.{Jump, Label, Let, Ret}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy._
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.ClassRef

sealed case class LocalEscape(var simpleEscape : Boolean = false, mutableList: mutable.MutableList[Local] = mutable.MutableList[Local]())

class EscapeAnalysis(config: tools.Config)(implicit top: Top) extends Pass {
  import EscapeAnalysis._

  private def updateMap(map: Map[Local, LocalEscape], locals: Set[Local]) = {
    locals.foreach { local =>
      map.get(local) match {
        case Some(x) => x.simpleEscape = true
        case _ =>
      }
    }
  }

  private def escape(map: Map[Local, LocalEscape], local: Local, visited: scala.collection.Set[Local] = scala.collection.Set[Local]()) : Boolean = {
    map.get(local) match {
      case Some(x) =>
        x.simpleEscape ||
          visited.intersect(x.mutableList.toSet).nonEmpty ||
          x.mutableList.foldLeft(false)((acc, dep) => acc ||
            escape(map, dep, visited + local))
      case None => false
    }
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    var t = false
    val escapeMap : mutable.Map[Local, LocalEscape] = mutable.Map[Local, LocalEscape]()

    val labels : Seq[Label] = insts.collect {
      case i : Label => i
    }

    insts foreach {
      case inst @ Let(local, op: Op.Classalloc) =>
        if(inst.show.contains("Simplest")) {
          t = true
          escapeMap.update(local, LocalEscape())
        }
      case Let(local, Op.Copy(v: Val.Local)) =>
        escapeMap.get(v.name) match {
          case Some(localEscape) =>
            localEscape.mutableList += local
            escapeMap.update(local, LocalEscape())
          case None =>
        }
      case  Let(_, op : Op.Store) => // Obvious Escape
        val vals = new AllVals()
        vals.onOp(op)
        //updateMap(escapeMap, vals.vals.toSet)
      case Ret(v : Val.Local) => escapeMap.get(v.name).foreach(_.simpleEscape = true)
      case Let(_, op: Op.Call) => // Obvious escape
        val vals = new AllVals()
        vals.onOp(op)
        //updateMap(escapeMap, vals.vals.toSet)
      case Jump(next @ Next.Label(name, args)) =>
        labels.find(l => l.name == name) match {
          case Some(label) =>
            label.params.zip(args).foreach {
              case (param, v : Val.Local) if escapeMap.keys.exists(_ == v.name) =>
                escapeMap.update(param.name, LocalEscape())
                escapeMap(v.name).mutableList += param.name
              case _ =>
            }
          case _ =>
        }
      case _ =>
    }

    if(t) {
      println(escapeMap)
    }

    val buf = new nir.Buffer()

    insts foreach {
      case inst @ Let(name, Op.Classalloc(ClassRef(node))) if inst.show.contains("Simplest") && !escape(escapeMap.toMap, name) =>
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
          Let(fresh(), Op.Store(Type.Ptr, dst, rtti.const))
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
