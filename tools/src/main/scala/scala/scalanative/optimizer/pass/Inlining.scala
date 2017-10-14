package scala.scalanative
package optimizer
package pass

import scala.scalanative.nir.Attr.{AlwaysInline, NoInline}
import scala.scalanative.nir.Inst.{Label, Let}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy.Method
import scala.scalanative.optimizer.analysis.ClassHierarchy._
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.MethodRef

class Inlining(config: tools.Config)(implicit top: Top) extends Pass {

  private val INST_TRESH = 0

  println(s"Inlining thresh $INST_TRESH")

  private def inlineGlobal(name: Global, inst: Inst, buf: nir.Buffer) = {
    top.nodes.get(name) match {
      case Some(node: Method) if shouldInlineMethod(node) =>
        buf ++= UpdateLabel(fresh, top).onInsts(node.insts)
      case _ => buf += inst
    }
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val buf = new nir.Buffer

    val ops = insts.collect {
      case Let(Local(id), op) => (id, op)
    }.toMap

    insts.foreach {
      case inst @ Let(_, Op.Call(_, Val.Global(name, _), _, _)) => inlineGlobal(name, inst, buf)

      case inst @ Let(_, Op.Call(_, Val.Local(Local(id), _), _, _)) =>
        ops.get(id) match {
          case Some(Op.Method(_, MethodRef(_: Class, meth))) if meth.isStatic => inlineGlobal(meth.name, inst, buf)
          case _ => buf += inst
        }

      case inst =>
        buf += inst
    }

    buf.toSeq
  }

  private def shouldInlineMethod(method: Method): Boolean = {
    if (method.attrs.isExtern || isRecursive(method)) return false
    if (method.attrs.inline == NoInline) return false
    method.attrs.inline == AlwaysInline || method.name.show.contains("::init") || method.insts.size < INST_TRESH
  }

  private def isRecursive(method: Method) = false

}

private class UpdateLabel(implicit fresh: Fresh, top: Top) extends Pass {

  override def onInst(inst: Inst): Inst = inst match {
    case Let(Local(_), op) => super.onInst(Let(fresh(), op))
    case Label(Local(_), params) => super.onInst(Label(fresh(), params))
    case _ => super.onInst(inst)
  }

  override def onVal(value: Val): Val = value match {
    case Val.Local(_, ty) => super.onVal(Val.Local(fresh(), onType(ty)))
    case _ => super.onVal(value)
  }

  override def onNext(next: Next): Next = next match {
    case Next.Label(Local(_), args) => super.onNext(Next.Label(fresh(), args))
    case Next.Case(v, _)     => super.onNext(Next.Case(v, fresh()))
    case _ => super.onNext(next)
  }

}

private object UpdateLabel {
  def apply(fresh: Fresh, top: Top) = new UpdateLabel()(fresh, top)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
