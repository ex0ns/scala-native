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

  private val MAX_DEPTH = 2
  private val INST_THRESH = 64
  private val MAX_INSTS = 10000

  /**
    * Inline a method
    *
    * If a method must be inlined (see `shouldInlineMethod`), add a JUMP to the method label as well as a new
    * label (for the inlined function to return) to the current instructions.
    *
    * Returns the list of instructions that needs to be inline (we don't append them to the buffer because we need
    * to run the inliner on them beforehand)
    *
    * @param method The node corresponding to the method to inline
    * @param inst The current call instruction
    * @param buffer Buffer of instructions
    * @param update The value (local name and type) of the call, we need it to create the label with the right local
    * @param unwind The unwind (needed for exception handling)
    * @param args Calls args, need to be forwarded to the Jump
    * @param currentSize The current size of the method
    * @return the inlined instructions
    */
  private def inlineMethod(method: Option[Node],
                           inst: Inst,
                           buffer: nir.Buffer,
                           update: Val.Local,
                           unwind: Next,
                           args: Seq[Val],
                           currentSize: Int): Seq[Inst] = {
    method match {
      case Some(method: Method) if shouldInlineMethod(method, currentSize) =>
        val phi = fresh()
        val updated = UpdateLabel(fresh, top, phi, unwind).onInsts(method.insts)

        val newLabel = updated.head.asInstanceOf[Label] // The first instruction must always be a label
        buffer += Jump(Next.Label(newLabel.name, args))
        buffer += Label(phi, Seq(update))

        updated
      case _ =>
        buffer += inst
        List()
    }
  }

  private def inlineMethod(name: Global,
                           inst: Inst,
                           buf: nir.Buffer,
                           update: Val.Local,
                           unwind: Next,
                           args: Seq[Val],
                           currentSize: Int): Seq[Inst] =
    inlineMethod(top.nodes.get(name), inst, buf, update, unwind, args, currentSize)

  override def onDefn(defn: Defn): Defn = {
    defn match {
      case Defn.Define(_, _, _, _) => super.onDefn(defn) // Required to initialize super.fresh
      case _ => defn
    }
  }

  /**
    * Method reference might be copied into new local name (Op.Copy).
    * we need to recurse from copy to copy until we reach a MethodRef
    * @param ops Map of available methods
    * @param id ID to look for
    * @return an option containing the Method (if any found)
    */
  private def resolveMethod(ops: Map[Local, Op], id: Local): Option[Method] = {
    ops.get(id) match {
      case Some(Op.Method(_, MethodRef(_: Class, meth))) => Some(meth)
      case Some(Op.Copy(Val.Local(local, _))) => resolveMethod(ops, local)
      case _ => scala.None // ?
    }
  }

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    val buffer = new nir.Buffer()
    buffer ++= inline(1, insts.length, insts, buffer)
    buffer.toSeq
  }

  /**
    * The core of the inlining pass.
    *
    * This method works as a worklist, as we want to be able to run the inliner on inlined instruction, we need
    * to keep track of the current depth level of inlining, we go through the current instructions, and either add
    * them to the output buffer (if no need to inline), or create a new sequence of inlined instructions that will
    * need to be inlined on the next pass.
    *
    * To avoid infinite inlining (in the case of recursion for instance), we need to keep track of the current
    * inlining depth.
    *
    * @param currentLevel The current level of inlining
    * @param currentSize The number of instructions currently in the buffer
    * @param insts The current instructions that might be inlined
    * @param buffer The output buffer
    * @return A new sequence of instructions that could be inlined (worklist)
    */
  private def inline(currentLevel: Int, currentSize: Int, insts: Seq[Inst], buffer: nir.Buffer): Seq[Inst] = {

    val ops = insts.collect {
      case Let(local, op: Op.Copy) => (local, op)
      case Let(local, op: Op.Method) => (local, op)
    }.toMap

    val (inlined, size) = insts.foldLeft((Seq[Inst](), currentSize)) { (acc, inst) =>
      val (inlined, size) = acc

      inst match {
        case Let(local, Op.Call(Type.Function(_, ret), Val.Global(name, _), args, unwind)) =>
          val method = inlineMethod(name, inst, buffer, Val.Local(local, ret), unwind, args, size)
          (inlined ++ method , size + method.size)
        case Let(local, Op.Call(Type.Function(_, ret), Val.Local(localRef, _), args, unwind)) =>
          val method = inlineMethod(resolveMethod(ops, localRef), inst, buffer, Val.Local(local, ret), unwind, args, size)
          (inlined ++ method, size + method.size)
        case _ =>
          buffer += inst
          acc
      }
    }

    if(currentLevel < MAX_DEPTH) inline(currentLevel+1, size, inlined, buffer)
    else inlined
  }

  private def shouldInlineMethod(method: Method, currentSize: Int): Boolean = {
    if (method.insts.size + currentSize >= MAX_INSTS) return false
    if (method.attrs.isExtern || !method.isStatic)
      return false
    if (method.attrs.inline == NoInline) return false
    method.attrs.inline == AlwaysInline || method.name.show
      .contains("::init") || method.insts.size < INST_THRESH
  }
}

/**
  * This pass does multiple things:
  *   - Update all labels with new fresh names
  *   - Convert Ret instructions to Jump
  *   - Handles exceptions (propagates the exception handler when inlining)
  */
private class UpdateLabel(
                           ret: Local,
                           unwind: Next)(implicit fresh: Fresh, top: Top)
  extends Pass {

  private val reassign = mutable.Map[Local, Local]()
  private val buf = new nir.Buffer

  private def updateLocal(old: Local): Local =
    reassign.getOrElseUpdate(old, fresh())

  override def onInsts(insts: Seq[Inst]): Seq[Inst] = {
    insts.foreach {
      case Ret(v) =>
        buf += Jump(Next.Label(ret, Seq(onVal(v))))
      case inst => buf += onInst(inst)
    }

    buf.toSeq
  }

  override def onInst(inst: Inst): Inst = inst match {
    case Let(l@Local(_), op@Op.Call(_, _, _, Next.None))
      if unwind != Next.None =>
      onOp(op) match {
        case op: Op.Call => Let(updateLocal(l), op.copy(unwind = unwind))
        case _ => inst
      }
    case Let(l@Local(_), op) => Let(updateLocal(l), onOp(op))
    case Label(l@Local(_), params) =>
      Label(updateLocal(l), params.map {
        case Val.Local(l@_, ty) => Val.Local(updateLocal(l), onType(ty))
      })
    case Throw(value: Val, Next.None) if unwind != Next.None =>
      Throw(onVal(value), unwind)
    case _ => super.onInst(inst)
  }

  override def onVal(value: Val): Val = value match {
    case Val.Local(l@_, ty) => Val.Local(updateLocal(l), onType(ty))
    case _ => super.onVal(value)
  }

  override def onNext(next: Next): Next = next match {
    case Next.Unwind(l@Local(_)) => Next.Unwind(updateLocal(l))
    case Next.Label(l@Local(_), args) =>
      Next.Label(updateLocal(l), args.map(onVal))
    case Next.Case(v, l) => Next.Case(onVal(v), updateLocal(l))
    case _ => super.onNext(next)
  }

}

private object UpdateLabel {
  def apply(fresh: Fresh,
            top: Top,
            ret: Local,
            unwind: Next) =
    new UpdateLabel(ret, unwind)(fresh, top)
}

object Inlining extends PassCompanion {

  override val depends = Seq()

  override def apply(config: tools.Config, top: Top) =
    new Inlining(config)(top)
}
