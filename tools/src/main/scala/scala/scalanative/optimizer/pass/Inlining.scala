package scala.scalanative
package optimizer
package pass

import scala.scalanative.nir.Attr.{AlwaysInline, NoInline}
import scala.scalanative.nir.Inst.{Label, Let}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy.Method
import scala.scalanative.optimizer.analysis.ClassHierarchy._

class Inlining(config: tools.Config)(implicit top: Top) extends Pass {

  private val INST_TRESH = 15

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val buf = new nir.Buffer

    insts.foreach {
      case inst @ Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _)) =>
        top.nodes.get(global) match {
          case Some(node: Method) if shouldInlineMethod(node) =>
            buf ++= UpdateLabel(fresh, top).onInsts(node.insts)
          case _ => buf += inst
        }
      case inst => buf += inst
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

private class UpdateLabel(implicit top: Top, fresh: Fresh) extends Pass {

  override def onInst(inst: Inst): Inst = inst match {
    case Let(Local(_), op)       => super.onInst(Let(op))
    case Label(Local(_), params) => super.onInst(Label(fresh(), params))
    case _                       => super.onInst(inst)
  }

  override def onVal(value: Val): Val = value match {
    case Val.Local(_, ty) => Val.Local(fresh(), onType(ty))
    case _                => value
  }

  override def onNext(next: Next): Next = next match {
    case _ => next
  }

}

private object UpdateLabel {
  def apply(fresh: Fresh, top: Top) = new UpdateLabel()(top, fresh)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
