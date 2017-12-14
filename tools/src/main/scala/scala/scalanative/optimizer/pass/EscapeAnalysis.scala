package scala.scalanative
package optimizer
package pass

import scala.collection.mutable
import scala.scalanative.nir.Inst.{Jump, Label, Let, Ret}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy._
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.ClassRef

sealed case class LocalEscape(simpleEscape: Boolean = false,
                              dependsOn: Seq[Local] = Seq[Local]())

class EscapeAnalysis(config: tools.Config)(implicit top: Top) extends Pass {
  import EscapeAnalysis._
  private type EscapeMap = Map[Local, LocalEscape]

  private def escape(map: EscapeMap,
                     local: Local,
                     visited: scala.collection.Set[Local] =
                       scala.collection.Set[Local]()): Boolean = {
    map.get(local).fold(false) { x =>
      x.simpleEscape ||
      visited.intersect(x.dependsOn.toSet).nonEmpty ||
      x.dependsOn.foldLeft(false)((acc, dep) =>
        acc ||
          escape(map, dep, visited + local))
    }
  }

  private def paramEscape(escapeMap: EscapeMap,
                          label: Label,
                          args: Seq[Val]) = {
    def updateMap(param: Val.Local, value: Val.Local) = {
      escapeMap.get(value.name).fold(Seq[(Local, LocalEscape)]()) {
        localEscape =>
          Seq((value.name,
               localEscape.copy(
                 dependsOn = localEscape.dependsOn :+ param.name)), // Update dependency
              (param.name, LocalEscape())) // Add the the local
      }
    }

    label.params
      .zip(args)
      .collect { case (param, v: Val.Local) => updateMap(param, v) }
      .flatten
      .toMap
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    var t = false

    val labels: Seq[Label] = insts.collect {
      case i: Label => i
    }

    def updateMap(map: EscapeMap, value: Val.Local)(
        f: LocalEscape => EscapeMap) = map.get(value.name).fold(map)(f)

    val escapeMap = insts.foldLeft(Map[Local, LocalEscape]()) {
      (escapeMap, inst) =>
        {
          inst match {
            case inst @ Let(local, op: Op.Classalloc) =>
              if (inst.show.contains("Simplest")) {
                t = true
                escapeMap + (local -> LocalEscape())
              } else escapeMap
            case Let(local, Op.Copy(v: Val.Local)) =>
              updateMap(escapeMap, v) { (localEscape: LocalEscape) =>
                escapeMap + (local -> LocalEscape(), v.name -> localEscape
                  .copy(dependsOn = localEscape.dependsOn :+ local))
              }
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
              updateMap(escapeMap, v) { (localEscape: LocalEscape) =>
                {
                  escapeMap + (v.name -> localEscape.copy(simpleEscape = true))
                }
              }
            case Let(_, op: Op.Call) => // Obvious escape
              val vals = new AllVals()
              vals.onOp(op)
              escapeMap
            case _ => escapeMap
          }
        }
    }

    if (t) {
      println(escapeMap)
    }

    val buf = new nir.Buffer()

    insts foreach {
      case inst @ Let(name, Op.Classalloc(ClassRef(node)))
          if inst.show.contains("Simplest") && !escape(escapeMap, name) =>
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
