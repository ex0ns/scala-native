package scala.scalanative
package optimizer
package pass

import scala.collection.mutable
import scala.scalanative.nir.Attr.{AlwaysInline, NoInline}
import scala.scalanative.nir.Inst.{Label, Let, Ret}
import scala.scalanative.nir.Op.{Copy, Stackalloc}
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy.{Method, _}
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.MethodRef

/**
  *
  * @param config
  * @param top
  */
class Inlining(config: tools.Config)(implicit top: Top) extends Pass {

  private val INST_TRESH = 0

  println(s"Inlining thresh $INST_TRESH")

  /**
    %3(%1 : class @B, %2 : int):
    %4 = iadd[int] int 5, %2 : int
    ret %4 : int

    Called using %8 = call[(class @B, int) => int] %7 : ptr(%5 : class @B, int 6)
    Here, as 6 is not a Local, we need to create a new Local for it (let's say %9)
    The method will create the map: Map(%1 -> %5, %2 -> %9), and produce the code (that will be inline):

    %9 = copy 6 : int
    %13 = iadd[int] int 5, %9 : int
    %8 = copy %13 : int

    Indeed, we need to remove the ret instruction and use the call's label to update its value
    *
    */
  private def inlineGlobal(name: Global, inst: Inst, buf: nir.Buffer, update: Local, args: Seq[Val]) = {
    top.nodes.get(name) match {
      case Some(node: Method) if shouldInlineMethod(node) =>
        // We create a map from Local to Local using the method's label
        val mapping = node.insts.head match {
          case Label(_, params) =>
            params.map(_.name).zip(args.map {
              case Val.Local(local, _) => local
              case other =>
                val t = fresh()
                buf += Let(t, Op.Copy(other))// What to do if not Local ?
                t
            }).toMap
          case _ => throw new Exception("Should inline only if this is a method")
        }

        val updated = UpdateLabel(fresh, top, mapping).onInsts(node.insts.tail) // Drop the Label()
        buf ++= updated.dropRight(1) // Drop the ret
        buf += Let(update, Op.Copy(updated.last.asInstanceOf[Ret].value)) // remove ret and store value // @TODO: remove this ugly asInstanceOf
      case _ => buf += inst
    }
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val buf = new nir.Buffer

    val ops = insts.collect {
      case Let(Local(id), op) => (id, op)
    }.toMap

    insts.foreach {
      case inst @ Let(local, Op.Call(_, Val.Global(name, _), args, _)) => inlineGlobal(name, inst, buf, local, args)

      case inst @ Let(local, Op.Call(_, Val.Local(Local(id), _), args, _)) =>
        ops.get(id) match {
          case Some(Op.Method(_, MethodRef(_: Class, meth))) if meth.isStatic =>
            inlineGlobal(meth.name, inst, buf, local, args)
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
    method.attrs.inline == AlwaysInline /*|| method.name.show.contains("::init") */|| method.insts.size < INST_TRESH
  }

  private def isRecursive(method: Method) = false

}

/**
  * Go through all instructions and update their Local value according to the map
  */
private class UpdateLabel(mapping: Map[Local, Local])(implicit fresh: Fresh, top: Top) extends Pass {

  val reassign =  mutable.Map[Local, Local](mapping.toSeq: _*)

  private def updateLocal(old: Local) : Local = reassign.getOrElseUpdate(old, fresh())

  override def onInst(inst: Inst): Inst = inst match {
    case Let(l @ Local(_), op) => Let(updateLocal(l), onOp(op))
    case Label(l @ Local(_), params) => Label(updateLocal(l), params.map {
      case Val.Local(l @ _, ty) => Val.Local(updateLocal(l), onType(ty))
    })
    case _ => super.onInst(inst)
  }

  override def onVal(value: Val): Val = value match {
    case Val.Local(l @ _, ty) => Val.Local(updateLocal(l), onType(ty))
    case _ => super.onVal(value)
  }

  override def onNext(next: Next): Next = next match {
    case Next.Label(l @ Local(_), args) => Next.Label(updateLocal(l), args.map(onVal))
    case Next.Case(v, l)     => Next.Case(onVal(v), updateLocal(l))
    case _ => super.onNext(next)
  }

}

private object UpdateLabel {
  def apply(fresh: Fresh, top: Top, mapping: Map[Local, Local]) = new UpdateLabel(mapping)(fresh, top)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
