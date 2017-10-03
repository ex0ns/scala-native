package scala.scalanative
package optimizer
package pass

import scala.scalanative.nir.Attr.AlwaysInline
import scala.scalanative.nir.Inst.Let
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy.Method
import scala.scalanative.optimizer.analysis.ClassHierarchy._

class Inlining(config: tools.Config)(implicit top: Top) extends Pass {

  private val updateLabelPass = UpdateLabel(config, top)

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val buf = new nir.Buffer

    insts.foreach {
      case inst @ Let(_, Op.Call(Type.Function(_, _), Val.Global(global, _), _, _)) => {
        top.nodes.get(global) match {
          case Some(node: Method) if shouldInlineMethod(node) => buf ++= updateLabelPass.onInsts(node.insts)
          case _ => buf += inst
        }
      }
      case inst => buf += inst
    }

    buf.toSeq
  }

  private def shouldInlineMethod(method: Method) : Boolean = {
    if(method.attrs.isExtern) return false
    method.attrs.inline == AlwaysInline || method.name.show.contains("::init")
  }

}

private class UpdateLabel(implicit top: Top) extends Pass {

  override def onInst(inst: Inst): Inst = inst match {
    case Let(Local(_), op) => Let(op)
    case inst => inst
  }

}

private object UpdateLabel extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new UpdateLabel()(top)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
