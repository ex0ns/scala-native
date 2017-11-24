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

  private val INST_THRESH                    = 4
  private val INST_MAX_INST_THRESH           = 200
  private val calls: mutable.HashSet[Global] = mutable.HashSet()

  private def createMapping(buf: nir.Buffer, label: Inst, args: Seq[Val]) = {
    def argsToLocal = args.map {
      case Val.Local(local, _) => local
      case other =>
        val label = fresh()
        buf += Let(label, Op.Copy(other))
        label
    }

    label match {
      case Label(_, params) =>
        params
          .map(_.name)
          .zip(argsToLocal)
          .toMap
      case _ =>
        throw new Exception("Should inline only if this is a method") // Is that even correct ?
    }
  }

  /**
   * %3(%1 : class @B, %2 : int):
   * %4 = iadd[int] int 5, %2 : int
   * ret %4 : int
   * *
   * Called using %8 = call[(class @B, int) => int] %7 : ptr(%5 : class @B, int 6)
   * Here, as 6 is not a Local, we need to create a new Local for it (let's say %9)
   * The method will create the map: Map(%1 -> %5, %2 -> %9), and produce the code (that will be inline):
   * *
   * %9 = copy 6 : int
   * %13 = iadd[int] int 5, %9 : int
   * %8 = copy %13 : int
   * *
   * Indeed, we need to remove the ret instruction and use the call's label to update its value
   *
   */
  private def inlineGlobal(method: Option[Node],
                           inst: Inst,
                           buf: nir.Buffer,
                           update: Val.Local,
                           unwind: Next,
                           args: Seq[Val]): Unit = {
    method match {
      case Some(method: Method) if shouldInlineMethod(method) =>
        //calls.add(method.name)
        val mapping = createMapping(buf, method.insts.head, args)
        val updated = UpdateLabel(fresh, top, update, unwind, mapping).onInsts(
          method.insts.tail)

        buf ++= updated
      case _ => buf += inst
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
      case defn @ Defn.Define(_, _, _, _) =>
        calls.clear()
        calls.add(defn.name)
        super.onDefn(defn)
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
        buf += inst
    }

    buf.toSeq
  }

  private def shouldInlineMethod(method: Method): Boolean = {
    if (method.attrs.isExtern || isRecursive(method) || !method.isStatic)
      return false
    if (method.attrs.inline == NoInline) return false
    method.attrs.inline == AlwaysInline || method.name.show
      .contains("::init") || method.insts.size < INST_THRESH
  }

  private def isRecursive(method: Method) = calls.contains(method.name)
}

/**
 * Go through all instructions and update their Local value according to the map
 */
private class UpdateLabel(
    ret: Val.Local,
    unwind: Next,
    mapping: Map[Local, Local])(implicit fresh: Fresh, top: Top)
    extends Pass {

  private val reassign = mutable.Map[Local, Local](mapping.toSeq: _*)
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
            unwind: Next,
            mapping: Map[Local, Local]) =
    new UpdateLabel(ret, unwind, mapping)(fresh, top)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
