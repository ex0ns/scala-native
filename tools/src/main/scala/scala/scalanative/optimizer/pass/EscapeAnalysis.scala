package scala.scalanative
package optimizer
package pass

import scala.collection.mutable
import scala.scalanative.nir.Inst._
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy._
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.ClassRef

class EscapeAnalysis(config: tools.Config)(implicit top: Top) extends Pass {
  import EscapeAnalysis._

  private sealed case class LocalEscape(var simpleEscape: Boolean = false,
                                        dependsOn: mutable.ListBuffer[Local] = mutable.ListBuffer[Local]()) {
    def escapes            = simpleEscape = true
    def addDep(dep: Local) = dependsOn += dep
  }

  private type EscapeMap = mutable.Map[Local, LocalEscape]

  private def escapes(map: EscapeMap, local: Local) : Boolean = {
    val toVisit = mutable.Stack[Local]()
    val visited = mutable.Stack[Local]()

    toVisit.push(local)

    while(toVisit.nonEmpty) {
      val current = toVisit.pop()
      visited.push(current)
      map.get(current) match {
        case Some(state) =>
          if(state.simpleEscape) return true
          if(visited.toSet.intersect(state.dependsOn.toSet).nonEmpty) return true

          if(state.dependsOn.isEmpty) visited.pop()
          toVisit.pushAll(state.dependsOn)

        case _ => visited.pop()
      }
    }
    false
  }

  private def addParamToMap(map: EscapeMap, param: Local, value: Local) = {
    map.getOrElseUpdate(param, LocalEscape())
    map.getOrElseUpdate(value, LocalEscape()).addDep(param)
  }

  private def markAsEscaped(map: EscapeMap, v: Local) = map.getOrElseUpdate(v, LocalEscape()).escapes

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val labels: Seq[Label] = insts.collect { case i: Label => i }

    val escapeMap = mutable.Map[Local, LocalEscape]()

    insts.foreach {
      case Let(local, _: Op.Classalloc) =>
        escapeMap.update(local, LocalEscape())

      case Let(local, Op.Copy(v: Val.Local)) =>
        escapeMap.getOrElseUpdate(local, LocalEscape())
        escapeMap.getOrElseUpdate(v.name, LocalEscape()).addDep(local)

      case Jump(Next.Label(name, args)) =>
        labels.find(l => l.name == name) match {
          case Some(label) =>
            label.params
              .zip(args)
              .collect { case (param, v: Val.Local) => addParamToMap(escapeMap, param.name, v.name) }
          case scala.None =>
        }
      case Ret(v: Val.Local) => markAsEscaped(escapeMap, v.name)
      case Throw(v: Val.Local, _) => markAsEscaped(escapeMap, v.name)
      case Let(_, Op.Store(_, _, v: Val.Local, _)) => markAsEscaped(escapeMap, v.name)

      case Let(_, op: Op.Call) =>
        op.args.collect { case a: Val.Local => a }.foreach(v => markAsEscaped(escapeMap, v.name))
      case _ =>
    }


    val buf = new nir.Buffer()

    val stackAllocs = insts.foldLeft(Seq[Inst]()) ((acc, inst) => inst match {
      case Let(name, Op.Classalloc(ClassRef(node)))
          if !escapes(escapeMap, name) =>

        val struct = node.layout.struct
        val size   = node.layout.size
        val rtti   = node.rtti
        val dst = Val.Local(name, Type.Ptr)

        buf ++= Seq(
          Let(fresh(),
              Op.Call(memsetSig,
                      memset,
                      Seq(
                        dst,
                        Val.Byte(0),
                        Val.Long(size),
                        Val.Int(1), // Align
                        Val.Bool(false) // Volatile
                      ),
                      Next.None)),
          Let(fresh(), Op.Store(Type.Ptr, dst, rtti.const))
        )
        acc :+ Let(name, Op.Stackalloc(struct, nir.Val.None))
      case inst @ _ =>
        buf += inst
        acc
    })

    val instructions = buf.toSeq
    (instructions.head +: stackAllocs) ++ instructions.tail
  }
}

object EscapeAnalysis extends PassCompanion {

  override val depends = Seq()

  val memsetSig = Type.Function(
    Seq(Type.Ptr, Type.Byte, Type.Long, Type.Int, Type.Bool),
    Type.Void)
  val memSetName = Global.Top("llvm.memset.p0i8.i64")
  val memset     = Val.Global(memSetName, memsetSig)

  override val injects =
    Seq(Defn.Declare(Attrs.None, memSetName, memsetSig))

  override def apply(config: tools.Config, top: Top) =
    new EscapeAnalysis(config)(top)
}

private class AllVals extends Pass {
  val vals: mutable.Set[Local] = mutable.Set[Local]()

  override def onVal(value: Val): Val = value match {
    case Val.Local(local, _) =>
      vals.add(local)
      value
    case _ => super.onVal(value)

  }

}