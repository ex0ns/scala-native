package scala.scalanative
package optimizer
package pass

import scala.collection.mutable
import scala.scalanative.nir.Attr.{AlwaysInline, NoInline}
import scala.scalanative.nir.Inst._
import scala.scalanative.nir._
import scala.scalanative.optimizer.analysis.ClassHierarchy.{Method, _}
import scala.scalanative.optimizer.analysis.ClassHierarchyExtractors.MethodRef

/**
 * Inline pass, inlines constructor calls, as well as method calls
 * that are marked as inline
 */
class Inlining(config: tools.Config)(implicit top: Top) extends Pass {

  private var size  = 0
  private val INST_THRESH                    = 4
  private val MAX_INSTS = 3000

  println(s"Inlining Threshold: $INST_THRESH")

  private def inlineGlobal(method: Option[Node],
                           inst: Inst,
                           buf: nir.Buffer,
                           update: Val.Local,
                           unwind: Next,
                           args: Seq[Val]): Unit = {
    method match {
      case Some(method: Method) if shouldInlineMethod(method) =>
        val updated = UpdateLabel(fresh, top, update, unwind).onInsts(
          method.insts)

        val newLabel = updated.head.asInstanceOf[Label]
        buf += Jump(Next.Label(newLabel.name, args))
        buf ++= updated
        size = size + updated.length
      case _ =>
        buf += inst
    }
  }

  private def inlineGlobal(name: Global,
                           inst: Inst,
                           buf: nir.Buffer,
                           update: Val.Local,
                           unwind: Next,
                           args: Seq[Val]): Unit =
    inlineGlobal(top.nodes.get(name), inst, buf, update, unwind, args)

  override def onDefn(defn: Defn): Defn = {
    defn match {
      case defn @ Defn.Define(_, _, _, _) => super.onDefn(defn)
      case _ =>
        defn
    }
  }

  def resolveMethod(ops: Map[Local, Op], id: Local) : Option[Method] = {
    ops.get(id) match {
      case Some(Op.Method(_, MethodRef(_: Class, meth))) => Some(meth)
      case Some(Op.Copy(Val.Local(local, _))) => resolveMethod(ops, local)
      case _ => scala.None // ?
    }
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
      size = insts.length
      val buf = new nir.Buffer

      val ops = insts.collect {
        case Let(local, op) => (local, op)
      }.toMap

      insts.foreach {
        case inst @ Let(local,
                        Op.Call(Type.Function(_, ret),
                                Val.Global(name, _),
                                args,
                                unwind)) =>
          inlineGlobal(name, inst, buf, Val.Local(local, ret), unwind, args)
        case inst @ Let(local,
                        Op.Call(Type.Function(_, ret),
                                Val.Local(localRef, _),
                                args,
                                unwind)) =>
              inlineGlobal(resolveMethod(ops, localRef),
                           inst,
                           buf,
                           Val.Local(local, ret),
                           unwind,
                           args)
        case inst =>
          size+=1
          buf += inst
      }
      buf.toSeq
  }

  private def shouldInlineMethod(method: Method): Boolean = {
    if (method.insts.size + size >= MAX_INSTS) return false
    if (method.attrs.isExtern || !method.isStatic)
      return false
    if (method.attrs.inline == NoInline) return false
    method.attrs.inline == AlwaysInline || method.name.show
      .contains("::init") || method.insts.size < INST_THRESH
  }
}

/**
 * Go through all instructions and update their Local value according to the map
 */
private class UpdateLabel(
    ret: Val.Local,
    unwind: Next)(implicit fresh: Fresh, top: Top)
    extends Pass {

  private val reassign = mutable.Map[Local, Local]()
  private val buf      = new nir.Buffer

  private def updateLocal(old: Local): Local =
    reassign.getOrElseUpdate(old, fresh())

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val phi = fresh()

    insts.foreach {
      case Ret(v) =>
        val copy = Let(fresh(), Op.Copy(onVal(v)))
        buf += copy
        buf += Jump(Next.Label(phi, Seq(Val.Local(copy.name, v.ty))))

      case inst => buf += onInst(inst)
    }

    buf += Label(phi, Seq(ret))

    buf.toSeq
  }

  override def onInst(inst: Inst): Inst = inst match {
    case Let(l @ Local(_), op @ Op.Call(_, _, _, Next.None))
        if unwind != Next.None =>
      onOp(op) match {
        case op: Op.Call => Let(updateLocal(l), op.copy(unwind = unwind))
        case _           => inst
      }
    case Let(l @ Local(_), op) => Let(updateLocal(l), onOp(op))
    case Label(l @ Local(_), params) =>
      Label(updateLocal(l), params.map {
        case Val.Local(l @ _, ty) => Val.Local(updateLocal(l), onType(ty))
      })
    case Throw(value: Val, Next.None) if unwind != Next.None =>
      Throw(onVal(value), unwind)
    case _ => super.onInst(inst)
  }

  override def onVal(value: Val): Val = value match {
    case Val.Local(l @ _, ty) => Val.Local(updateLocal(l), onType(ty))
    case _                    => super.onVal(value)
  }

  override def onNext(next: Next): Next = next match {
    case Next.Unwind(l @ Local(_)) => Next.Unwind(updateLocal(l))
    case Next.Label(l @ Local(_), args) =>
      Next.Label(updateLocal(l), args.map(onVal))
    case Next.Case(v, l) => Next.Case(onVal(v), updateLocal(l))
    case _               => super.onNext(next)
  }

}

private object UpdateLabel {
  def apply(fresh: Fresh,
            top: Top,
            ret: Val.Local,
            unwind: Next) =
    new UpdateLabel(ret, unwind)(fresh, top)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
