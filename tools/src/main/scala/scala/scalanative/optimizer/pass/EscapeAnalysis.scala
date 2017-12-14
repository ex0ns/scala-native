package scala.scalanative
package optimizer
package pass

import scala.collection.mutable
import scala.scalanative.nir.Inst.{Jump, Label, Let, Ret}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy._
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.ClassRef

class EscapeAnalysis(config: tools.Config)(implicit top: Top) extends Pass {
  import EscapeAnalysis._

  private sealed case class LocalEscape(simpleEscape: Boolean = false,
                                        dependsOn: Seq[Local] = Seq[Local]()) {
    def escapes = LocalEscape(simpleEscape = true, dependsOn)
    def addDep(dep: Local) = LocalEscape(simpleEscape, dependsOn :+ dep)
  }

  private type EscapeMap = Map[Local, LocalEscape]

  private def escapes(map: EscapeMap,
                      local: Local,
                      visited: scala.collection.Set[Local] =
                        scala.collection.Set[Local]()): Boolean = {
    def escapes0(x: LocalEscape) =
      x.simpleEscape ||
        visited.intersect(x.dependsOn.toSet).nonEmpty ||
        x.dependsOn.foldLeft(false)((acc, dep) =>
          acc || escapes(map, dep, visited + local))

    map.get(local).fold(false)(escapes0)
  }

  private def paramEscape(escapeMap: EscapeMap,
                          label: Label,
                          args: Seq[Val]) = {
    def addParamToMap(param: Val.Local, value: Val.Local) = {
      escapeMap.get(value.name).fold(Map[Local, LocalEscape]()) { localEscape =>
        Map(
          value.name -> localEscape.addDep(param.name),
          param.name -> LocalEscape()
        )
      }
    }

    label.params
      .zip(args)
      .collect { case (param, v: Val.Local) => addParamToMap(param, v) }
      .flatten
      .toMap
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val labels: Seq[Label] = insts.collect { case i: Label => i }

    def updateMap(map: EscapeMap, value: Val.Local)(
        f: LocalEscape => EscapeMap) = map.get(value.name).fold(map)(f)

    val escapeMap = insts.foldLeft(Map[Local, LocalEscape]()) {
      (escapeMap, inst) =>
        {
          inst match {
            case Let(local, op: Op.Classalloc) =>
              escapeMap + (local -> LocalEscape())
            case Let(local, Op.Copy(v: Val.Local)) =>
              updateMap(escapeMap, v) { localEscape => escapeMap + (local -> LocalEscape(), v.name -> localEscape.addDep(local)) }
            case Jump(Next.Label(name, args)) =>
              labels.find(l => l.name == name).fold(escapeMap) { label =>
                escapeMap ++ paramEscape(escapeMap, label, args)
              }
            // Cases for obvious escape
            case Let(_, op: Op.Store) => // Obvious Escape
              val vals = new AllVals()
              vals.onOp(op)
              escapeMap
            case Ret(v: Val.Local) =>
              updateMap(escapeMap, v) { localEscape => escapeMap + (v.name -> localEscape.escapes) }
            case Let(_, op: Op.Call) => // Obvious escape
              val vals = new AllVals()
              vals.onOp(op)
              escapeMap
            case _ => escapeMap
          }
        }
    }

    val buf = new nir.Buffer()

    insts foreach {
      case inst @ Let(name, Op.Classalloc(ClassRef(node)))
          if inst.show.contains("Simplest") && !escapes(escapeMap, name) =>
        val struct = node.layout.struct
        val size   = node.layout.size
        val rtti   = node.rtti

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
                      ),
                      Next.None)),
          Let(fresh(), Op.Store(Type.Ptr, dst, rtti.const))
        )
      case inst @ _ => buf += inst
    }

    buf.toSeq
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
