package scala.scalanative
package nscplugin

import scala.collection.mutable
import scala.reflect.internal.Flags._
import scalanative.nir._
import scalanative.util.unsupported
import scalanative.util.ScopedVar.scoped
import scalanative.nscplugin.NirPrimitives._

trait NirGenExpr { self: NirGenPhase =>
  import global._
  import definitions._
  import treeInfo.hasSynthCaseSymbol
  import nirAddons._
  import nirDefinitions._
  import SimpleType.{fromType, fromSymbol}

  final case class ValTree(value: nir.Val)    extends Tree
  final case class ContTree(f: () => nir.Val) extends Tree

  class FixupBuffer(implicit fresh: Fresh) extends nir.Buffer {
    private var labeled = false

    override def +=(inst: Inst): Unit = {
      inst match {
        case inst: nir.Inst.Label =>
          if (labeled) {
            unreachable
          }
          labeled = true
        case _ =>
          if (!labeled) {
            label(fresh())
          }
          labeled = !inst.isInstanceOf[nir.Inst.Cf]
      }
      super.+=(inst)
    }

    override def ++=(insts: Seq[Inst]): Unit =
      insts.foreach { inst =>
        this += inst
      }

    override def ++=(other: nir.Buffer): Unit =
      this ++= other.toSeq
  }

  class ExprBuffer(implicit fresh: Fresh) extends FixupBuffer { buf =>
    def genExpr(tree: Tree): Val = tree match {
      case EmptyTree =>
        Val.Unit
      case ValTree(value) =>
        value
      case ContTree(f) =>
        f()
      case tree: Block =>
        genBlock(tree)
      case tree: LabelDef =>
        genLabelDef(tree)
      case tree: ValDef =>
        genValDef(tree)
      case tree: If =>
        genIf(tree)
      case tree: Match =>
        genMatch(tree)
      case tree: Try =>
        genTry(tree)
      case tree: Throw =>
        genThrow(tree)
      case tree: Return =>
        genReturn(tree)
      case tree: Literal =>
        genLiteral(tree)
      case tree: ArrayValue =>
        genArrayValue(tree)
      case tree: This =>
        genThis(tree)
      case tree: Ident =>
        genIdent(tree)
      case tree: Select =>
        genSelect(tree)
      case tree: Assign =>
        genAssign(tree)
      case tree: Typed =>
        genTyped(tree)
      case tree: Function =>
        genFunction(tree)
      case tree: ApplyDynamic =>
        genApplyDynamic(tree)
      case tree: Apply =>
        genApply(tree)
      case _ =>
        abort(
          "Unexpected tree in genExpr: " + tree + "/" + tree.getClass +
            " at: " + tree.pos)
    }

    def genBlock(block: Block): Val = {
      val Block(stats, last) = block

      def isCaseLabelDef(tree: Tree) =
        tree.isInstanceOf[LabelDef] && hasSynthCaseSymbol(tree)

      def translateMatch(last: LabelDef) = {
        val (prologue, cases) = stats.span(s => !isCaseLabelDef(s))
        val labels            = cases.map { case label: LabelDef => label }
        genMatch(prologue, labels :+ last)
      }

      last match {
        case label: LabelDef if isCaseLabelDef(label) =>
          translateMatch(label)

        case Apply(TypeApply(Select(label: LabelDef, nme.asInstanceOf_Ob), _),
                   _) if isCaseLabelDef(label) =>
          translateMatch(label)

        case _ =>
          stats.foreach(genExpr(_))
          genExpr(last)
      }
    }

    def genLabelDef(label: LabelDef): Val = {
      assert(label.params.length == 0)
      buf.jump(Next(curMethodEnv.enterLabel(label)))
      genLabel(label)
    }

    def genLabel(label: LabelDef): Val = {
      val local = curMethodEnv.resolveLabel(label)
      val params = label.params.map { id =>
        val local = Val.Local(fresh(), genType(id.tpe, box = false))
        curMethodEnv.enter(id.symbol, local)
        local
      }

      buf.label(local, params)
      genExpr(label.rhs)
    }

    def genTailRecLabel(dd: DefDef, isStatic: Boolean, label: LabelDef): Val = {
      val local = curMethodEnv.resolveLabel(label)
      val params = label.params.zip(genParamSyms(dd, isStatic)).map {
        case (lparam, mparamopt) =>
          val local = Val.Local(fresh(), genType(lparam.tpe, box = false))
          curMethodEnv.enter(lparam.symbol, local)
          mparamopt.foreach(curMethodEnv.enter(_, local))
          local
      }

      buf.label(local, params)
      if (isStatic) {
        genExpr(label.rhs)
      } else {
        scoped(curMethodThis := Some(params.head)) {
          genExpr(label.rhs)
        }
      }
    }

    def genValDef(vd: ValDef): Val = {
      val rhs       = genExpr(vd.rhs)
      val isMutable = curMethodInfo.mutableVars.contains(vd.symbol)
      if (!isMutable) {
        curMethodEnv.enter(vd.symbol, rhs)
        Val.Unit
      } else {
        val ty    = genType(vd.symbol.tpe, box = false)
        val alloc = curMethodEnv.resolve(vd.symbol)
        buf.store(ty, alloc, rhs)
      }
    }

    def genIf(tree: If): Val = {
      val If(cond, thenp, elsep) = tree
      val retty                  = genType(tree.tpe, box = false)
      genIf(retty, cond, thenp, elsep)
    }

    def genIf(retty: nir.Type, condp: Tree, thenp: Tree, elsep: Tree): Val = {
      val thenn, elsen, mergen = fresh()
      val mergev               = Val.Local(fresh(), retty)

      val cond = genExpr(condp)
      buf.branch(cond, Next(thenn), Next(elsen))
      locally {
        buf.label(thenn)
        val thenv = genExpr(thenp)
        buf.jump(mergen, Seq(thenv))
      }
      locally {
        buf.label(elsen)
        val elsev = genExpr(elsep)
        buf.jump(mergen, Seq(elsev))
      }
      buf.label(mergen, Seq(mergev))
      mergev
    }

    def genMatch(m: Match): Val = {
      val Match(scrutp, allcaseps) = m

      // Extract switch cases and assign unique names to them.
      val caseps: Seq[(Local, Val, Tree)] = allcaseps.flatMap {
        case CaseDef(Ident(nme.WILDCARD), _, _) =>
          Seq()
        case CaseDef(pat, guard, body) =>
          assert(guard.isEmpty)
          val vals: Seq[Val] = pat match {
            case lit: Literal =>
              List(genLiteralValue(lit))
            case Alternative(alts) =>
              alts.map {
                case lit: Literal => genLiteralValue(lit)
              }
            case _ =>
              Nil
          }
          vals.map((fresh(), _, body))
      }

      // Extract default case.
      val defaultp: Tree = allcaseps.collectFirst {
        case c @ CaseDef(Ident(nme.WILDCARD), _, body) => body
      }.get

      // Generate some more fresh names and types.
      val retty       = genType(m.tpe, box = false)
      val casenexts   = caseps.map { case (n, v, _) => Next.Case(v, n) }
      val defaultnext = Next(fresh())
      val merge       = fresh()
      val mergev      = Val.Local(fresh(), retty)

      // Generate code for the switch and its cases.
      val scrut = genExpr(scrutp)
      buf.switch(scrut, defaultnext, casenexts)
      buf.label(defaultnext.name)
      val defaultres = genExpr(defaultp)
      buf.jump(merge, Seq(defaultres))
      caseps.foreach {
        case (n, _, expr) =>
          buf.label(n)
          val caseres = genExpr(expr)
          buf.jump(merge, Seq(caseres))
      }
      buf.label(merge, Seq(mergev))
      mergev
    }

    def genMatch(prologue: List[Tree], lds: List[LabelDef]): Val = {
      // Generate prologue expressions.
      prologue.foreach(genExpr(_))

      // Enter symbols for all labels and jump to the first one.
      lds.foreach(curMethodEnv.enterLabel)
      buf.jump(Next(curMethodEnv.resolveLabel(lds.head)))

      // Generate code for all labels and return value of the last one.
      lds.map(genLabel(_)).last
    }

    def genTry(tree: Try): Val = tree match {
      case Try(expr, catches, finalizer)
          if catches.isEmpty && finalizer.isEmpty =>
        genExpr(expr)
      case Try(expr, catches, finalizer) =>
        val retty = genType(tree.tpe, box = false)
        genTry(retty, expr, catches, finalizer)
    }

    def genTry(retty: nir.Type,
               expr: Tree,
               catches: List[Tree],
               finallyp: Tree): Val = {
      val unwind = fresh()
      val excn    = fresh()
      val normaln = fresh()
      val mergen  = fresh()
      val excv    = Val.Local(fresh(), Rt.Object)
      val mergev  = Val.Local(fresh(), retty)

      // Nested code gen to separate out try/catch-related instructions.
      val nested = new ExprBuffer
      locally {
        scoped(curUnwind := Next.Unwind(unwind)) {
          nested.label(normaln)
          val res = nested.genExpr(expr)
          nested.jump(mergen, Seq(res))
        }
      }
      locally {
        nested.label(unwind, Seq(excv))
        val res = nested.genTryCatch(retty, excv, mergen, catches)
        nested.jump(mergen, Seq(res))
      }

      // Append finally to the try/catch instructions and merge them back.
      val insts =
        if (finallyp.isEmpty) {
          nested.toSeq
        } else {
          genTryFinally(finallyp, nested.toSeq)
        }

      // Append try/catch instructions to the outher instruction buffer.
      buf.jump(Next(normaln))
      buf ++= insts
      buf.label(mergen, Seq(mergev))
      mergev
    }

    def genTryCatch(retty: nir.Type,
                    exc: Val,
                    mergen: Local,
                    catches: List[Tree]): Val = {
      val cases = catches.map {
        case CaseDef(pat, _, body) =>
          val (excty, symopt) = pat match {
            case Typed(Ident(nme.WILDCARD), tpt) =>
              (genType(tpt.tpe, box = false), None)
            case Ident(nme.WILDCARD) =>
              (genType(ThrowableClass.tpe, box = false), None)
            case Bind(_, _) =>
              (genType(pat.symbol.tpe, box = false), Some(pat.symbol))
          }
          val f = { () =>
            symopt.foreach { sym =>
              val cast = buf.as(excty, exc)
              curMethodEnv.enter(sym, cast)
            }
            val res = genExpr(body)
            buf.jump(mergen, Seq(res))
            Val.Unit
          }
          (excty, f)
      }

      def wrap(cases: Seq[(nir.Type, () => Val)]): Val =
        cases match {
          case Seq() =>
            buf.raise(exc, curUnwind)
            Val.Unit
          case (excty, f) +: rest =>
            val cond = buf.is(excty, exc)
            genIf(retty,
                  ValTree(cond),
                  ContTree(f),
                  ContTree(() => wrap(rest)))
        }

      wrap(cases)
    }

    def genTryFinally(finallyp: Tree, insts: Seq[nir.Inst]): Seq[Inst] = {
      val labels =
        insts.collect {
          case Inst.Label(n, _) => n
        }.toSet
      def internal(cf: Inst.Cf) = cf match {
        case inst @ Inst.Jump(n) =>
          labels.contains(n.name)
        case inst @ Inst.If(_, n1, n2) =>
          labels.contains(n1.name) && labels.contains(n2.name)
        case inst @ Inst.Switch(_, n, ns) =>
          labels.contains(n.name) && ns.forall(n => labels.contains(n.name))
        case inst @ Inst.Throw(_, n) =>
          (n ne Next.None) && labels.contains(n.name)
        case _ =>
          false
      }

      val finalies = new ExprBuffer
      val transformed = insts.map {
        case cf: Inst.Cf if internal(cf) =>
          // We don't touch control-flow within try/catch block.
          cf
        case cf: Inst.Cf =>
          // All control-flow edges that jump outside the try/catch block
          // must first go through finally block if it's present. We generate
          // a new copy of the finally handler for every edge.
          val finallyn = fresh()
          finalies.label(finallyn)
          val res = finalies.genExpr(finallyp)
          finalies += cf
          // The original jump outside goes through finally block first.
          Inst.Jump(Next(finallyn))
        case inst =>
          inst
      }
      transformed ++ finalies.toSeq
    }

    def genThrow(tree: Throw): Val = {
      val Throw(exprp) = tree
      val res          = genExpr(exprp)
      buf.raise(res, curUnwind)
      Val.Unit
    }

    def genReturn(tree: Return): Val = {
      val Return(exprp) = tree
      val res           = genExpr(exprp)
      buf.ret(res)
      Val.Unit
    }

    def genLiteral(lit: Literal): Val = {
      val value = lit.value
      value.tag match {
        case UnitTag | NullTag | BooleanTag | ByteTag | ShortTag | CharTag |
            IntTag | LongTag | FloatTag | DoubleTag | StringTag =>
          genLiteralValue(lit)

        case ClazzTag =>
          genBoxClass(genTypeValue(value.typeValue))

        case EnumTag =>
          genStaticMember(value.symbolValue)
      }
    }

    def genLiteralValue(lit: Literal): Val = {
      val value = lit.value
      value.tag match {
        case UnitTag =>
          Val.Unit
        case NullTag =>
          Val.Null
        case BooleanTag =>
          if (value.booleanValue) Val.True else Val.False
        case ByteTag =>
          Val.Byte(value.intValue.toByte)
        case ShortTag | CharTag =>
          Val.Short(value.intValue.toShort)
        case IntTag =>
          Val.Int(value.intValue)
        case LongTag =>
          Val.Long(value.longValue)
        case FloatTag =>
          Val.Float(value.floatValue)
        case DoubleTag =>
          Val.Double(value.doubleValue)
        case StringTag =>
          Val.String(value.stringValue)
      }
    }

    def genArrayValue(av: ArrayValue): Val = {
      val ArrayValue(tpt, elems) = av

      val len       = Literal(Constant(elems.length))
      val elemcode  = genPrimCode(tpt.tpe)
      val modulesym = RuntimeArrayModule(elemcode)
      val methsym   = RuntimeArrayAllocMethod(elemcode)
      val alloc     = genApplyModuleMethod(modulesym, methsym, Seq(len))

      if (elems.nonEmpty) {
        val values = genSimpleArgs(elems)

        values.zipWithIndex.foreach {
          case (v, i) =>
            val idx = Literal(Constant(i))

            genApplyMethod(RuntimeArrayUpdateMethod(elemcode),
                          statically = true,
                          alloc,
                          Seq(idx, ValTree(v)))
        }
      }

      alloc
    }

    def genThis(tree: This): Val =
      if (curMethodThis.nonEmpty && tree.symbol == curClassSym.get) {
        curMethodThis.get.get
      } else {
        genModule(tree.symbol)
      }

    def genModule(sym: Symbol): Val =
      buf.module(genTypeName(sym), curUnwind)

    def genIdent(tree: Ident): Val = {
      val sym = tree.symbol
      if (curMethodInfo.mutableVars.contains(sym)) {
        val ty = genType(sym.tpe, box = false)
        buf.load(ty, curMethodEnv.resolve(sym))
      } else if (sym.isModule) {
        buf.module(genTypeName(sym), curUnwind)
      } else {
        curMethodEnv.resolve(sym)
      }
    }

    def genSelect(tree: Select): Val = {
      val Select(qualp, selp) = tree

      val sym   = tree.symbol
      val owner = sym.owner
      if (sym.isModule) {
        buf.module(genTypeName(sym), curUnwind)
      } else if (sym.isStaticMember) {
        genStaticMember(sym)
      } else if (sym.isMethod) {
        genApplyMethod(sym, statically = false, qualp, Seq())
      } else if (owner.isStruct) {
        val index = owner.info.decls.filter(_.isField).toList.indexOf(sym)
        val qual  = genExpr(qualp)
        buf.extract(qual, Seq(index))
      } else {
        val ty   = genType(tree.symbol.tpe, box = false)
        val qual = genExpr(qualp)
        val name = genFieldName(tree.symbol)
        val elem =
          if (sym.owner.isExternModule) {
            Val.Global(name, Type.Ptr)
          } else {
            buf.field(qual, name)
          }
        buf.load(ty, elem)
      }
    }

    def genStaticMember(sym: Symbol): Val = {
      if (sym == BoxedUnit_UNIT) {
        Val.Unit
      } else {
        val ty     = genType(sym.tpe, box = false)
        val module = buf.module(genTypeName(sym.owner), curUnwind)
        genApplyMethod(sym, statically = true, module, Seq(ValTree(module)))
      }
    }

    def genAssign(tree: Assign): Val = {
      val Assign(lhsp, rhsp) = tree

      lhsp match {
        case sel @ Select(qualp, _) =>
          val ty   = genType(sel.tpe, box = false)
          val qual = genExpr(qualp)
          val rhs  = genExpr(rhsp)
          val name = genFieldName(sel.symbol)
          val elem =
            if (sel.symbol.owner.isExternModule) {
              Val.Global(name, Type.Ptr)
            } else {
              buf.field(qual, name)
            }
          buf.store(ty, elem, rhs)

        case id: Ident =>
          val ty  = genType(id.tpe, box = false)
          val rhs = genExpr(rhsp)
          val ptr = curMethodEnv.resolve(id.symbol)
          buf.store(ty, ptr, rhs)
      }
    }

    def genTyped(tree: Typed): Val = tree match {
      case Typed(Super(_, _), _) =>
        curMethodThis.get.get
      case Typed(expr, _) =>
        genExpr(expr)
    }

    def genFunction(tree: Function): Val =
      unsupported(tree)

    def genApplyDynamic(app: ApplyDynamic): Val = {
      val ApplyDynamic(obj, args) = app
      val sym                     = app.symbol

      val params = sym.tpe.params

      val isEqEqOrBangEq = (sym.name == EqEqMethodName || sym.name == NotEqMethodName) &&
        params.size == 1

      // If the method is '=='or '!=' generate class equality instead of dyn-call
      if (isEqEqOrBangEq) {
        val neg  = sym.name == nme.ne || sym.name == NotEqMethodName
        val last = genClassEquality(obj, args.head, ref = false, negated = neg)
        buf.box(nir.Type.Class(nir.Global.Top("java.lang.Boolean")), last)
      } else {
        val self = genExpr(obj)
        genApplyDynamic(sym, self, args)
      }
    }

    def genApplyDynamic(sym: Symbol, self: Val, argsp: Seq[Tree]): Val = {
      val methodSig = genMethodSig(sym).asInstanceOf[Type.Function]
      val params    = sym.tpe.params

      def isArrayLikeOp = {
        sym.name == nme.update &&
        params.size == 2 && params.head.tpe.typeSymbol == IntClass
      }

      def genDynCall(arrayUpdate: Boolean) = {

        // In the case of an array update we need to manually erase the return type.
        val methodName =
          if (arrayUpdate) "update_i32_java.lang.Object"
          else nir.Global.genSignature(genMethodName(sym))

        val sig =
          Type.Function(
            methodSig.args.head ::
              methodSig.args.tail.map(ty => Type.box.getOrElse(ty, ty)).toList,
            nir.Type.Class(nir.Global.Top("java.lang.Object")))

        val callerType = methodSig.args.head
        val boxedArgTypes =
          methodSig.args.tail.map(ty => nir.Type.box.getOrElse(ty, ty)).toList

        val retType   = nir.Type.Class(nir.Global.Top("java.lang.Object"))
        val signature = nir.Type.Function(callerType :: boxedArgTypes, retType)
        val args      = genMethodArgs(sym, argsp, boxedArgTypes)

        val method = buf.dynmethod(self, methodName.toString)
        val values = self +: args

        val call = buf.call(signature, method, values, curUnwind)
        buf.as(nir.Type.box.getOrElse(methodSig.ret, methodSig.ret), call)
      }

      // If the signature matches an array update, tests at runtime if it really is an array update.
      if (isArrayLikeOp) {
        val cond = ContTree { () =>
          buf.is(nir.Type.Class(
                   nir.Global.Top("scala.scalanative.runtime.ObjectArray")),
                 self)
        }
        val thenp = ContTree { () =>
          genDynCall(arrayUpdate = true)
        }
        val elsep = ContTree { () =>
          genDynCall(arrayUpdate = false)
        }
        genIf(nir.Type.Class(nir.Global.Top("java.lang.Object")),
              cond,
              thenp,
              elsep)

      } else {
        genDynCall(arrayUpdate = false)
      }
    }

    def genApply(app: Apply): Val = {
      val Apply(fun, args) = app

      fun match {
        case _: TypeApply =>
          genApplyTypeApply(app)
        case Select(Super(_, _), _) =>
          genApplyMethod(fun.symbol,
                        statically = true,
                        curMethodThis.get.get,
                        args)
        case Select(New(_), nme.CONSTRUCTOR) =>
          genApplyNew(app)
        case _ =>
          val sym = fun.symbol

          if (sym.isLabel) {
            genApplyLabel(app)
          } else if (scalaPrimitives.isPrimitive(sym)) {
            genApplyPrimitive(app)
          } else if (currentRun.runDefinitions.isBox(sym)) {
            val arg = args.head
            genApplyBox(arg.tpe, arg)
          } else if (currentRun.runDefinitions.isUnbox(sym)) {
            genApplyUnbox(app.tpe, args.head)
          } else {
            val Select(receiverp, _) = fun
            genApplyMethod(fun.symbol, statically = false, receiverp, args)
          }
      }
    }

    def genApplyLabel(tree: Tree): Val = {
      val Apply(fun, argsp)   = tree
      val Val.Local(label, _) = curMethodEnv.resolve(fun.symbol)
      val args                = genSimpleArgs(argsp)
      buf.jump(label, args)
      Val.Unit
    }

    def genApplyBox(st: SimpleType, argp: Tree): Val = {
      val value = genExpr(argp)

      buf.box(genBoxType(st), value)
    }

    def genApplyUnbox(st: SimpleType, argp: Tree): Val = {
      val value = genExpr(argp)
      value.ty match {
        case _: scalanative.nir.Type.I | _: scalanative.nir.Type.F =>
          // No need for unboxing, fixing some slack generated by the general
          // purpose Scala compiler.
          value
        case _ =>
          buf.unbox(genBoxType(st), value)
      }
    }

    def genApplyPrimitive(app: Apply): Val = {
      import scalaPrimitives._

      val Apply(fun @ Select(receiver, _), args) = app

      val sym  = app.symbol
      val code = scalaPrimitives.getPrimitive(sym, receiver.tpe)

      if (isArithmeticOp(code) || isLogicalOp(code) || isComparisonOp(code)) {
        genSimpleOp(app, receiver :: args, code)
      } else if (code == CONCAT) {
        genStringConcat(receiver, args.head)
      } else if (code == HASH) {
        genHashCode(args.head)
      } else if (isArrayOp(code) || code == ARRAY_CLONE) {
        genArrayOp(app, code)
      } else if (nirPrimitives.isPtrOp(code)) {
        genPtrOp(app, code)
      } else if (nirPrimitives.isFunPtrOp(code)) {
        genFunPtrOp(app, code)
      } else if (isCoercion(code)) {
        genCoercion(app, receiver, code)
      } else if (code == SYNCHRONIZED) {
        genSynchronized(app)
      } else if (code == CCAST) {
        genCastOp(app)
      } else if (code == SIZEOF || code == TYPEOF) {
        genOfOp(app, code)
      } else if (code == STACKALLOC) {
        genStackalloc(app)
      } else if (code == CQUOTE) {
        genCQuoteOp(app)
      } else if (code == BOXED_UNIT) {
        Val.Unit
      } else if (code >= DIV_UINT && code <= INT_TO_ULONG) {
        genUnsignedOp(app, code)
      } else if (code == SELECT) {
        genSelectOp(app)
      } else {
        abort(
          "Unknown primitive operation: " + sym.fullName + "(" +
            fun.symbol.simpleName + ") " + " at: " + (app.pos))
      }
    }

    lazy val jlClassName     = nir.Global.Top("java.lang.Class")
    lazy val jlClass         = nir.Type.Class(jlClassName)
    lazy val jlClassCtorName = jlClassName member "init_ptr"
    lazy val jlClassCtorSig =
      nir.Type.Function(Seq(jlClass, Type.Ptr), nir.Type.Unit)
    lazy val jlClassCtor = nir.Val.Global(jlClassCtorName, nir.Type.Ptr)

    def genBoxClass(typeVal: Val): Val = {
      val alloc = buf.classalloc(jlClassName)
      buf.call(jlClassCtorSig, jlClassCtor, Seq(alloc, typeVal), curUnwind)
      alloc
    }

    def numOfType(num: Int, ty: nir.Type): Val = ty match {
      case Type.Byte | Type.UByte               => Val.Byte(num.toByte)
      case Type.Short | Type.UShort | Type.Char => Val.Short(num.toShort)
      case Type.Int | Type.UInt                 => Val.Int(num)
      case Type.Long | Type.ULong               => Val.Long(num.toLong)
      case Type.Float                           => Val.Float(num.toFloat)
      case Type.Double                          => Val.Double(num.toDouble)
      case _                                    => unsupported(s"num = $num, ty = ${ty.show}")
    }

    def genSimpleOp(app: Apply, args: List[Tree], code: Int): Val = {
      val retty = genType(app.tpe, box = false)

      args match {
        case List(right)       => genUnaryOp(code, right, retty)
        case List(left, right) => genBinaryOp(code, left, right, retty)
        case _                 => abort("Too many arguments for primitive function: " + app)
      }
    }

    def negateInt(value: nir.Val): Val =
      buf.bin(Bin.Isub, value.ty, numOfType(0, value.ty), value)
    def negateFloat(value: nir.Val): Val =
      buf.bin(Bin.Fsub, value.ty, numOfType(0, value.ty), value)
    def negateBits(value: nir.Val): Val =
      buf.bin(Bin.Xor, value.ty, numOfType(-1, value.ty), value)
    def negateBool(value: nir.Val): Val =
      buf.bin(Bin.Xor, Type.Bool, Val.True, value)

    def genUnaryOp(code: Int, rightp: Tree, opty: nir.Type): Val = {
      import scalaPrimitives._

      val right   = genExpr(rightp)
      val coerced = genCoercion(right, right.ty, opty)

      (opty, code) match {
        case (_: Type.I | _: Type.F, POS) => coerced
        case (_: Type.I, NOT)             => negateBits(coerced)
        case (_: Type.F, NEG)             => negateFloat(coerced)
        case (_: Type.I, NEG)             => negateInt(coerced)
        case (_: Type.I, ZNOT)            => negateBool(coerced)
        case _                            => abort("Unknown unary operation code: " + code)
      }
    }

    def genBinaryOp(code: Int, left: Tree, right: Tree, retty: nir.Type): Val = {
      import scalaPrimitives._

      val lty  = genType(left.tpe, box = false)
      val rty  = genType(right.tpe, box = false)
      val opty = binaryOperationType(lty, rty)

      val binres = opty match {
        case _: Type.F =>
          code match {
            case ADD =>
              genBinaryOp(Op.Bin(Bin.Fadd, _, _, _), left, right, opty)
            case SUB =>
              genBinaryOp(Op.Bin(Bin.Fsub, _, _, _), left, right, opty)
            case MUL =>
              genBinaryOp(Op.Bin(Bin.Fmul, _, _, _), left, right, opty)
            case DIV =>
              genBinaryOp(Op.Bin(Bin.Fdiv, _, _, _), left, right, opty)
            case MOD =>
              genBinaryOp(Op.Bin(Bin.Frem, _, _, _), left, right, opty)

            case EQ =>
              genBinaryOp(Op.Comp(Comp.Feq, _, _, _), left, right, opty)
            case NE =>
              genBinaryOp(Op.Comp(Comp.Fne, _, _, _), left, right, opty)
            case LT =>
              genBinaryOp(Op.Comp(Comp.Flt, _, _, _), left, right, opty)
            case LE =>
              genBinaryOp(Op.Comp(Comp.Fle, _, _, _), left, right, opty)
            case GT =>
              genBinaryOp(Op.Comp(Comp.Fgt, _, _, _), left, right, opty)
            case GE =>
              genBinaryOp(Op.Comp(Comp.Fge, _, _, _), left, right, opty)

            case _ =>
              abort(
                "Unknown floating point type binary operation code: " + code)
          }

        case _: Type.I =>
          code match {
            case ADD =>
              genBinaryOp(Op.Bin(Bin.Iadd, _, _, _), left, right, opty)
            case SUB =>
              genBinaryOp(Op.Bin(Bin.Isub, _, _, _), left, right, opty)
            case MUL =>
              genBinaryOp(Op.Bin(Bin.Imul, _, _, _), left, right, opty)
            case DIV =>
              genBinaryOp(Op.Bin(Bin.Sdiv, _, _, _), left, right, opty)
            case MOD =>
              genBinaryOp(Op.Bin(Bin.Srem, _, _, _), left, right, opty)

            case OR =>
              genBinaryOp(Op.Bin(Bin.Or, _, _, _), left, right, opty)
            case XOR =>
              genBinaryOp(Op.Bin(Bin.Xor, _, _, _), left, right, opty)
            case AND =>
              genBinaryOp(Op.Bin(Bin.And, _, _, _), left, right, opty)
            case LSL =>
              genBinaryOp(Op.Bin(Bin.Shl, _, _, _), left, right, opty)
            case LSR =>
              genBinaryOp(Op.Bin(Bin.Lshr, _, _, _), left, right, opty)
            case ASR =>
              genBinaryOp(Op.Bin(Bin.Ashr, _, _, _), left, right, opty)

            case EQ =>
              genBinaryOp(Op.Comp(Comp.Ieq, _, _, _), left, right, opty)
            case NE =>
              genBinaryOp(Op.Comp(Comp.Ine, _, _, _), left, right, opty)
            case LT =>
              genBinaryOp(Op.Comp(Comp.Slt, _, _, _), left, right, opty)
            case LE =>
              genBinaryOp(Op.Comp(Comp.Sle, _, _, _), left, right, opty)
            case GT =>
              genBinaryOp(Op.Comp(Comp.Sgt, _, _, _), left, right, opty)
            case GE =>
              genBinaryOp(Op.Comp(Comp.Sge, _, _, _), left, right, opty)

            case ZOR =>
              genIf(retty, left, Literal(Constant(true)), right)
            case ZAND =>
              genIf(retty, left, right, Literal(Constant(false)))

            case _ =>
              abort("Unknown integer type binary operation code: " + code)
          }

        case _: Type.RefKind =>
          def genEquals(ref: Boolean, negated: Boolean) = (left, right) match {
            // If null is present on either side, we must always
            // generate reference equality, regardless of where it
            // was called with == or eq. This shortcut is not optional.
            case (Literal(Constant(null)), _)
               | (_, Literal(Constant(null))) =>
              genClassEquality(left, right, ref = true, negated = negated)
            case _ =>
              genClassEquality(left, right, ref = ref, negated = negated)
          }

          code match {
            case EQ =>
              genEquals(ref = false, negated = false)
            case NE =>
              genEquals(ref = false, negated = true)
            case ID =>
              genEquals(ref = true, negated = false)
            case NI =>
              genEquals(ref = true, negated = true)

            case _ =>
              abort("Unknown reference type operation code: " + code)
          }

        case Type.Ptr =>
          code match {
            case EQ | ID =>
              genBinaryOp(Op.Comp(Comp.Ieq, _, _, _), left, right, opty)
            case NE | NI =>
              genBinaryOp(Op.Comp(Comp.Ine, _, _, _), left, right, opty)
          }

        case ty =>
          abort("Unknown binary operation type: " + ty)
      }

      genCoercion(binres, binres.ty, retty)
    }

    def genBinaryOp(op: (nir.Type, Val, Val) => Op,
                    leftp: Tree,
                    rightp: Tree,
                    opty: nir.Type): Val = {
      val leftty       = genType(leftp.tpe, box = false)
      val left         = genExpr(leftp)
      val leftcoerced  = genCoercion(left, leftty, opty)
      val rightty      = genType(rightp.tpe, box = false)
      val right        = genExpr(rightp)
      val rightcoerced = genCoercion(right, rightty, opty)

      buf.let(op(opty, leftcoerced, rightcoerced))
    }

    def genClassEquality(leftp: Tree,
                         rightp: Tree,
                         ref: Boolean,
                         negated: Boolean): Val = {
      val left = genExpr(leftp)

      if (ref) {
        val right = genExpr(rightp)
        val comp  = if (negated) Comp.Ine else Comp.Ieq
        buf.comp(comp, Rt.Object, left, right)
      } else {
        val thenn, elsen, mergen = fresh()
        val mergev               = Val.Local(fresh(), nir.Type.Bool)

        val isnull = buf.comp(Comp.Ieq, Rt.Object, left, Val.Null)
        buf.branch(isnull, Next(thenn), Next(elsen))
        locally {
          buf.label(thenn)
          val right = genExpr(rightp)
          val thenv = buf.comp(Comp.Ieq, Rt.Object, right, Val.Null)
          buf.jump(mergen, Seq(thenv))
        }
        locally {
          buf.label(elsen)
          val elsev = genApplyMethod(NObjectEqualsMethod,
                                    statically = false,
                                    left,
                                    Seq(rightp))
          buf.jump(mergen, Seq(elsev))
        }
        buf.label(mergen, Seq(mergev))
        if (negated) negateBool(mergev) else mergev
      }
    }

    def binaryOperationType(lty: nir.Type, rty: nir.Type) = (lty, rty) match {
      case (nir.Type.Ptr, _: nir.Type.RefKind) =>
        lty
      case (_: nir.Type.RefKind, nir.Type.Ptr) =>
        rty
      case (nir.Type.Bool, nir.Type.Bool) =>
        nir.Type.Bool
      case (nir.Type.I(lwidth, _), nir.Type.I(rwidth, _))
          if lwidth < 32 && rwidth < 32 =>
        nir.Type.Int
      case (nir.Type.I(lwidth, _), nir.Type.I(rwidth, _)) =>
        if (lwidth >= rwidth) lty else rty
      case (nir.Type.I(_, _), nir.Type.F(_)) =>
        rty
      case (nir.Type.F(_), nir.Type.I(_, _)) =>
        lty
      case (nir.Type.F(lwidth), nir.Type.F(rwidth)) =>
        if (lwidth >= rwidth) lty else rty
      case (_: nir.Type.RefKind, _: nir.Type.RefKind) =>
        Rt.Object
      case (ty1, ty2) if ty1 == ty2 =>
        ty1
      case _ =>
        abort(s"can't perform binary operation between $lty and $rty")
    }

    def genStringConcat(leftp: Tree, rightp: Tree): Val = {
      def stringify(sym: Symbol, value: Val): Val = {
        val cond = ContTree { () =>
          buf.comp(Comp.Ieq, Rt.Object, value, Val.Null)
        }
        val thenp = ContTree { () =>
          Val.String("null")
        }
        val elsep = ContTree { () =>
          if (sym == StringClass) {
            value
          } else {
            val meth = Object_toString
            genApplyMethod(meth, statically = false, value, Seq())
          }
        }
        genIf(Rt.String, cond, thenp, elsep)
      }

      val left = {
        val typesym = leftp.tpe.typeSymbol
        val unboxed = genExpr(leftp)
        val boxed   = boxValue(typesym, unboxed)
        stringify(typesym, boxed)
      }

      val right = {
        val typesym = rightp.tpe.typeSymbol
        val boxed   = genExpr(rightp)
        stringify(typesym, boxed)
      }

      genApplyMethod(String_+, statically = true, left, Seq(ValTree(right)))
    }

    def genHashCode(argp: Tree): Val = {
      val arg    = boxValue(argp.tpe, genExpr(argp))
      val isnull = buf.comp(Comp.Ieq, Rt.Object, arg, Val.Null)
      val cond   = ValTree(isnull)
      val thenp  = ValTree(Val.Int(0))
      val elsep  = ContTree { () =>
        val meth = NObjectHashCodeMethod
        genApplyMethod(meth, statically = false, arg, Seq())
      }
      genIf(Type.Int, cond, thenp, elsep)
    }

    def genArrayOp(app: Apply, code: Int): Val = {
      import scalaPrimitives._

      val Apply(Select(arrayp, _), argsp) = app

      val array    = genExpr(arrayp)
      def elemcode = genArrayCode(arrayp.tpe)
      val method =
        if (code == ARRAY_CLONE) {
          RuntimeArrayCloneMethod(elemcode)
        } else if (scalaPrimitives.isArrayGet(code)) {
          RuntimeArrayApplyMethod(elemcode)
        } else if (scalaPrimitives.isArraySet(code)) {
          RuntimeArrayUpdateMethod(elemcode)
        } else {
          RuntimeArrayLengthMethod(elemcode)
        }

      genApplyMethod(method, statically = true, array, argsp)
    }

    def boxValue(st: SimpleType, value: Val): Val = {
      if (genPrimCode(st.sym) == 'O') {
        value
      } else {
        genApplyBox(st, ValTree(value))
      }
    }

    def unboxValue(st: SimpleType, partial: Boolean, value: Val): Val = {
      val code = genPrimCode(st)

      code match {
        // Results of asInstanceOfs are partially unboxed, meaning
        // that non-standard value types remain to be boxed.
        case _ if partial && 'a' <= code && code <= 'z' =>
          value
        case 'O' =>
          value
        case _ =>
          genApplyUnbox(st, ValTree(value))
      }
    }

    def genPtrOp(app: Apply, code: Int): Val = {
      val Apply(sel @ Select(ptrp, _), argsp) = app

      val ptr = genExpr(ptrp)

      (code, argsp) match {
        case (PTR_LOAD, Seq(tagp)) =>
          val st    = unwrapTag(tagp)
          val ty    = genType(st, box = false)
          val value = buf.load(ty, ptr)
          boxValue(st, value)

        case (PTR_STORE, Seq(valuep, tagp)) =>
          val st      = unwrapTag(tagp)
          val ty      = genType(st, box = false)
          val value   = genExpr(valuep)
          val unboxed = unboxValue(st, partial = false, value)
          buf.store(ty, ptr, unboxed)

        case (PTR_ADD, Seq(offsetp, tagp)) =>
          val st     = unwrapTag(tagp)
          val ty     = genType(st, box = false)
          val offset = genExpr(offsetp)
          buf.elem(ty, ptr, Seq(offset))

        case (PTR_SUB, Seq(argp, tagp)) =>
          val st  = unwrapTag(tagp)
          val ty  = genType(st, box = false)
          val sym = argp.tpe.typeSymbol
          sym match {
            case IntClass =>
              val offset = genExpr(argp)
              val neg    = negateInt(offset)
              buf.elem(ty, ptr, Seq(neg))

            case PtrClass =>
              // Pointers in Scala Native are untyped and modeled as `i8*`.
              // Pointer substraction therefore explicitly divide the byte
              // offset by the size of pointer type.
              val ptrInt     = buf.conv(nir.Conv.Ptrtoint, nir.Type.Long, ptr)
              val ptrArg     = genExpr(argp)
              val ptrArgInt  = buf.conv(nir.Conv.Ptrtoint, nir.Type.Long, ptrArg)
              val byteOffset = buf.bin(Bin.Isub, nir.Type.Long, ptrInt, ptrArgInt)
              val sizeOf     = buf.sizeof(ty)
              buf.bin(Bin.Sdiv, nir.Type.Long, byteOffset, sizeOf)
          }

        case (PTR_APPLY, Seq(offsetp, tagp)) =>
          val st     = unwrapTag(tagp)
          val ty     = genType(st, box = false)
          val offset = genExpr(offsetp)
          val elem   = buf.elem(ty, ptr, Seq(offset))
          val value  = buf.load(ty, elem)
          boxValue(st, value)

        case (PTR_UPDATE, Seq(offsetp, valuep, tagp)) =>
          val st      = unwrapTag(tagp)
          val ty      = genType(st, box = false)
          val offset  = genExpr(offsetp)
          val value   = genExpr(valuep)
          val unboxed = unboxValue(st, partial = false, value)
          val elem    = buf.elem(ty, ptr, Seq(offset))
          buf.store(ty, elem, unboxed)

        case (PTR_FIELD, Seq(tagp, _)) =>
          val st    = unwrapTag(tagp)
          val ty    = genType(st, box = false)
          val index = PtrFieldMethod.indexOf(sel.symbol)
          val path  = Seq(nir.Val.Int(0), nir.Val.Int(index))
          buf.elem(ty, ptr, path)
      }
    }

    def genFunPtrOp(app: Apply, code: Int): Val = code match {
      case FUN_PTR_CALL =>
        val Apply(sel @ Select(funp, _), allargsp) = app

        val arity = CFunctionPtrApply.indexOf(sel.symbol)

        val (argsp, tagsp) = allargsp.splitAt(arity)

        val fun    = genExpr(funp)
        val tagsts = tagsp.map(unwrapTag)
        val tagtys = tagsts.map(genType(_, box = false))
        val sig    = Type.Function(tagtys.init, tagtys.last)

        val args = mutable.UnrolledBuffer.empty[nir.Val]

        tagsts.init.zip(argsp).foreach {
          case (st, argp) =>
            args += unboxValue(st, partial = false, genExpr(argp))
        }

        buf.call(sig, fun, args, curUnwind)

      case FUN_PTR_FROM =>
        val Apply(_, Seq(MaybeBlock(Typed(ctor, funtpt))))           = app
        val Apply(Select(New(tpt), termNames.CONSTRUCTOR), ctorargs) = ctor

        assert(ctorargs.isEmpty,
               s"Can't get function pointer to a closure with captures: ${ctorargs} in application ${app}")

        curStatBuffer.genFunctionPtrForwarder(tpt.tpe.typeSymbol)

      case _ =>
        util.unreachable
    }

    def castConv(fromty: nir.Type, toty: nir.Type): Option[nir.Conv] =
      (fromty, toty) match {
        case (_: Type.I, Type.Ptr)                   => Some(nir.Conv.Inttoptr)
        case (Type.Ptr, _: Type.I)                   => Some(nir.Conv.Ptrtoint)
        case (_: Type.RefKind, Type.Ptr)             => Some(nir.Conv.Bitcast)
        case (Type.Ptr, _: Type.RefKind)             => Some(nir.Conv.Bitcast)
        case (_: Type.RefKind, _: Type.I)            => Some(nir.Conv.Ptrtoint)
        case (_: Type.I, _: Type.RefKind)            => Some(nir.Conv.Inttoptr)
        case (Type.I(w1, _), Type.F(w2)) if w1 == w2 => Some(nir.Conv.Bitcast)
        case (Type.F(w1), Type.I(w2, _)) if w1 == w2 => Some(nir.Conv.Bitcast)
        case _ if fromty == toty                     => None
        case _ =>
          unsupported(s"cast from $fromty to $toty")
      }

    def genCastOp(app: Apply): Val = {
      val Apply(Select(Apply(_, List(valuep)), _), List(fromtagp, totagp)) = app

      val fromst = unwrapTag(fromtagp)
      val tost   = unwrapTag(totagp)
      val fromty = genType(fromst, box = false)
      val toty   = genType(tost, box = false)
      val value  = genExpr(valuep)
      val from   = unboxValue(fromst, partial = false, value)
      val conv   = castConv(fromty, toty).fold(from)(buf.conv(_, toty, from))

      boxValue(tost, conv)
    }

    def genOfOp(app: Apply, code: Int): Val = {
      val Apply(_, Seq(tagp)) = app

      val st = unwrapTag(tagp)

      code match {
        case SIZEOF => buf.sizeof(genType(st, box = false))
        case TYPEOF => genTypeValue(st)
        case _      => util.unreachable
      }
    }

    def genStackalloc(app: Apply): Val = {
      val (sizeopt, tagp) = app match {
        case Apply(_, Seq(tagp)) =>
          (None, tagp)
        case Apply(_, Seq(sizep, tagp)) =>
          (Some(sizep), tagp)
      }
      val ty   = genType(unwrapTag(tagp), box = false)
      val size = sizeopt.fold[Val](Val.None)(genExpr(_))

      buf.stackalloc(ty, size)
    }

    def genCQuoteOp(app: Apply): Val = {
      app match {
        // Sometimes I really miss quasiquotes.
        //
        // case q"""
        //   scala.scalanative.native.`package`.CQuote(
        //     new StringContext(scala.this.Predef.wrapRefArray(
        //       Array[String]{${str: String}}.$asInstanceOf[Array[Object]]()
        //     ))
        //   ).c()
        // """ =>
        case Apply(
            Select(
            Apply(
            _,
            List(
            Apply(_,
                  List(
                  Apply(_,
                        List(
                        Apply(TypeApply(
                              Select(ArrayValue(
                                     _, List(Literal(Constant(str: String)))),
                                     _),
                              _),
                              _))))))),
            _),
            _) =>
          Val.Const(Val.Chars(str.replace("\\n", "\n").replace("\\r", "\r")))

        case _ =>
          unsupported(app)
      }
    }

    def genUnsignedOp(app: Tree, code: Int): Val = app match {
      case Apply(_, Seq(argp)) =>
        assert(code >= BYTE_TO_UINT && code <= INT_TO_ULONG)

        val ty  = genType(app.tpe, box = false)
        val arg = genExpr(argp)

        buf.conv(Conv.Zext, ty, arg)

      case Apply(_, Seq(leftp, rightp)) =>
        val bin = code match {
          case DIV_UINT | DIV_ULONG => nir.Bin.Udiv
          case REM_UINT | REM_ULONG => nir.Bin.Urem
        }
        val ty    = genType(leftp.tpe, box = false)
        val left  = genExpr(leftp)
        val right = genExpr(rightp)

        buf.bin(bin, ty, left, right)
    }

    def genSelectOp(app: Tree): Val = {
      val Apply(_, Seq(condp, thenp, elsep, tagp)) = app

      val st    = unwrapTag(tagp)
      val cond  = genExpr(condp)
      val then_ = unboxValue(st, partial = false, genExpr(thenp))
      val else_ = unboxValue(st, partial = false, genExpr(elsep))
      val sel   = buf.let(Op.Select(cond, then_, else_))

      boxValue(st, sel)
    }

    def genSynchronized(app: Apply): Val = {
      val Apply(Select(receiverp, _), List(argp)) = app

      val monitor =
        genApplyModuleMethod(RuntimeModule, GetMonitorMethod, Seq(receiverp))
      val enter = genApplyMethod(RuntimeMonitorEnterMethod,
                                statically = true,
                                monitor,
                                Seq())
      val arg = genExpr(argp)
      val exit = genApplyMethod(RuntimeMonitorExitMethod,
                               statically = true,
                               monitor,
                               Seq())

      arg
    }

    def genCoercion(app: Apply, receiver: Tree, code: Int): Val = {
      val rec            = genExpr(receiver)
      val (fromty, toty) = coercionTypes(code)

      genCoercion(rec, fromty, toty)
    }

    def genCoercion(value: Val, fromty: nir.Type, toty: nir.Type): Val = {
      if (fromty == toty) {
        value
      } else {
        val conv = (fromty, toty) match {
          case (nir.Type.Ptr, _: nir.Type.RefKind) =>
            Conv.Bitcast
          case (_: nir.Type.RefKind, nir.Type.Ptr) =>
            Conv.Bitcast
          case (nir.Type.I(fromw, froms), nir.Type.I(tow, tos)) =>
            if (fromw < tow) {
              if (froms) {
                Conv.Sext
              } else {
                Conv.Zext
              }
            } else if (fromw > tow) {
              Conv.Trunc
            } else {
              Conv.Bitcast
            }
          case (nir.Type.I(_, true), _: nir.Type.F) =>
            Conv.Sitofp
          case (nir.Type.I(_, false), _: nir.Type.F) =>
            Conv.Uitofp
          case (_: nir.Type.F, nir.Type.I(_, true)) =>
            Conv.Fptosi
          case (_: nir.Type.F, nir.Type.I(_, false)) =>
            Conv.Fptoui
          case (nir.Type.Double, nir.Type.Float) =>
            Conv.Fptrunc
          case (nir.Type.Float, nir.Type.Double) =>
            Conv.Fpext
        }
        buf.conv(conv, toty, value)
      }
    }

    def coercionTypes(code: Int): (nir.Type, nir.Type) = {
      import scalaPrimitives._

      code match {
        case B2B => (nir.Type.Byte, nir.Type.Byte)
        case B2S => (nir.Type.Byte, nir.Type.Short)
        case B2C => (nir.Type.Byte, nir.Type.Char)
        case B2I => (nir.Type.Byte, nir.Type.Int)
        case B2L => (nir.Type.Byte, nir.Type.Long)
        case B2F => (nir.Type.Byte, nir.Type.Float)
        case B2D => (nir.Type.Byte, nir.Type.Double)

        case S2B => (nir.Type.Short, nir.Type.Byte)
        case S2S => (nir.Type.Short, nir.Type.Short)
        case S2C => (nir.Type.Short, nir.Type.Char)
        case S2I => (nir.Type.Short, nir.Type.Int)
        case S2L => (nir.Type.Short, nir.Type.Long)
        case S2F => (nir.Type.Short, nir.Type.Float)
        case S2D => (nir.Type.Short, nir.Type.Double)

        case C2B => (nir.Type.Char, nir.Type.Byte)
        case C2S => (nir.Type.Char, nir.Type.Short)
        case C2C => (nir.Type.Char, nir.Type.Char)
        case C2I => (nir.Type.Char, nir.Type.Int)
        case C2L => (nir.Type.Char, nir.Type.Long)
        case C2F => (nir.Type.Char, nir.Type.Float)
        case C2D => (nir.Type.Char, nir.Type.Double)

        case I2B => (nir.Type.Int, nir.Type.Byte)
        case I2S => (nir.Type.Int, nir.Type.Short)
        case I2C => (nir.Type.Int, nir.Type.Char)
        case I2I => (nir.Type.Int, nir.Type.Int)
        case I2L => (nir.Type.Int, nir.Type.Long)
        case I2F => (nir.Type.Int, nir.Type.Float)
        case I2D => (nir.Type.Int, nir.Type.Double)

        case L2B => (nir.Type.Long, nir.Type.Byte)
        case L2S => (nir.Type.Long, nir.Type.Short)
        case L2C => (nir.Type.Long, nir.Type.Char)
        case L2I => (nir.Type.Long, nir.Type.Int)
        case L2L => (nir.Type.Long, nir.Type.Long)
        case L2F => (nir.Type.Long, nir.Type.Float)
        case L2D => (nir.Type.Long, nir.Type.Double)

        case F2B => (nir.Type.Float, nir.Type.Byte)
        case F2S => (nir.Type.Float, nir.Type.Short)
        case F2C => (nir.Type.Float, nir.Type.Char)
        case F2I => (nir.Type.Float, nir.Type.Int)
        case F2L => (nir.Type.Float, nir.Type.Long)
        case F2F => (nir.Type.Float, nir.Type.Float)
        case F2D => (nir.Type.Float, nir.Type.Double)

        case D2B => (nir.Type.Double, nir.Type.Byte)
        case D2S => (nir.Type.Double, nir.Type.Short)
        case D2C => (nir.Type.Double, nir.Type.Char)
        case D2I => (nir.Type.Double, nir.Type.Int)
        case D2L => (nir.Type.Double, nir.Type.Long)
        case D2F => (nir.Type.Double, nir.Type.Float)
        case D2D => (nir.Type.Double, nir.Type.Double)
      }
    }

    def genApplyTypeApply(app: Apply): Val = {
      val Apply(TypeApply(fun @ Select(receiverp, _), targs), _) = app

      val ty    = genType(targs.head.tpe, box = true)
      val value = genExpr(receiverp)
      val boxed = boxValue(receiverp.tpe, value)

      fun.symbol match {
        case Object_isInstanceOf =>
          buf.is(ty, boxed)

        case Object_asInstanceOf =>
          if (boxed.ty == ty) {
            boxed
          } else {
            val cast = buf.as(ty, boxed)
            unboxValue(app.tpe, partial = true, cast)
          }
      }
    }

    def genApplyNew(app: Apply): Val = {
      val Apply(fun @ Select(New(tpt), nme.CONSTRUCTOR), args) = app

      SimpleType.fromType(tpt.tpe) match {
        case SimpleType(ArrayClass, Seq(targ)) =>
          genApplyNewArray(genPrimCode(targ), args)

        case st if st.isStruct =>
          genApplyNewStruct(st, args)

        case st @ SimpleType(UByteClass | UIntClass | UShortClass | ULongClass,
                             Seq())
            // We can't just compare the curClassSym with RuntimeBoxesModule
            // as it's not the same when you're actually compiling Boxes module.
            if curClassSym.fullName.toString != "scala.scalanative.runtime.Boxes" =>
          genApplyBox(st, args.head)

        case SimpleType(cls, Seq()) =>
          genApplyNew(cls, fun.symbol, args)

        case SimpleType(sym, targs) =>
          unsupported(s"unexpected new: $sym with targs $targs")
      }
    }

    def genApplyNewStruct(st: SimpleType, argsp: Seq[Tree]): Val = {
      val ty       = genType(st, box = false)
      val args     = genSimpleArgs(argsp)
      var res: Val = Val.Undef(ty)

      args.zipWithIndex.foreach {
        case (value, index) =>
          res = buf.insert(res, value, Seq(index))
      }

      res
    }

    def genApplyNewArray(elemcode: Char, argsp: Seq[Tree]): Val = {
      val module = RuntimeArrayModule(elemcode)
      val meth   = RuntimeArrayAllocMethod(elemcode)

      genApplyModuleMethod(module, meth, argsp)
    }

    def genApplyNew(clssym: Symbol, ctorsym: Symbol, args: List[Tree]): Val = {
      val alloc = buf.classalloc(genTypeName(clssym))
      val call  = genApplyMethod(ctorsym, statically = true, alloc, args)
      alloc
    }

    def genApplyModuleMethod(module: Symbol,
                            method: Symbol,
                            args: Seq[Tree]): Val = {
      val self = genModule(module)
      genApplyMethod(method, statically = true, self, args)
    }

    def genApplyMethod(sym: Symbol,
                      statically: Boolean,
                      selfp: Tree,
                      argsp: Seq[Tree]): Val = {
      if (sym.owner.isExternModule && sym.hasFlag(ACCESSOR)) {
        genApplyExternAccessor(sym, argsp)
      } else {
        val self = genExpr(selfp)
        genApplyMethod(sym, statically, self, argsp)
      }
    }

    def genApplyExternAccessor(sym: Symbol, argsp: Seq[Tree]): Val = {
      argsp match {
        case Seq() =>
          val ty   = genMethodSig(sym).ret
          val name = genMethodName(sym)
          val elem = Val.Global(name, Type.Ptr)
          buf.load(ty, elem)

        case Seq(value) =>
          unsupported(argsp)
      }
    }

    def genApplyMethod(sym: Symbol,
                      statically: Boolean,
                      self: Val,
                      argsp: Seq[Tree]): Val = {
      val owner = sym.owner
      val name  = genMethodName(sym)
      val sig   = genMethodSig(sym)
      val argsPt =
        if (owner.isExternModule || owner.isImplClass)
          sig.args
        else
          sig.args.tail
      val args = genMethodArgs(sym, argsp, argsPt)
      val method =
        if (statically || owner.isStruct || owner.isExternModule) {
          Val.Global(name, nir.Type.Ptr)
        } else {
          buf.method(self, name)
        }
      val values =
        if (owner.isExternModule || owner.isImplClass)
          args
        else
          self +: args

      buf.call(sig, method, values, curUnwind)
    }

    def genSimpleArgs(argsp: Seq[Tree]): Seq[Val] =
      genSimpleArgsWithPt(argsp, argsp.map(_ => None))

    def genSimpleArgsWithPt(
        argsp: Seq[Tree],
        pts: Seq[Option[scalanative.nir.Type]]): Seq[Val] = {
      val res = mutable.UnrolledBuffer.empty[Val]

      argsp.zip(pts).foreach {
        case (argp, ptopt) =>
          val value = genExpr(argp)
          ptopt.fold {
            res += value
          } { pt =>
            // Under certain circumstances e.g., the result of the c-function
            // pointer dereference being used in a position where an object
            // reference is objected, nir code generator leaves a primitive
            // value, since the Scala compiler didn't box it. Such applications
            // have to be augmented depending on the expected type of
            // the function.
            (value.ty, pt) match {
              case (ty: nir.Type.I, _: nir.Type.RefKind) =>
                res += nir.Type.box
                  .get(ty)
                  .map(buf.box(_, value))
                  .getOrElse(value)
              case (ty: nir.Type.F, _: nir.Type.RefKind) =>
                res += nir.Type.box
                  .get(ty)
                  .map(buf.box(_, value))
                  .getOrElse(value)
              case _ =>
                res += value
            }
          }
      }

      res
    }

    def genMethodArgs(sym: Symbol,
                      argsp: Seq[Tree],
                      argsPt: Seq[nir.Type]): Seq[Val] =
      if (!sym.owner.isExternModule) {
        genSimpleArgsWithPt(argsp, argsPt.map(Some(_)))
      } else {
        val wereRepeated = exitingPhase(currentRun.typerPhase) {
          for {
            params <- sym.tpe.paramss
            param  <- params
          } yield {
            param.name -> isScalaRepeatedParamType(param.tpe)
          }
        }.toMap

        val res = mutable.UnrolledBuffer.empty[Val]

        argsp.zip(sym.tpe.params).foreach {
          case (argp, paramSym) =>
            val wasRepeated = wereRepeated.getOrElse(paramSym.name, false)
            if (wasRepeated) {
              res ++= genExpandRepeatedArg(argp).get
            } else {
              res += genExpr(argp)
            }
        }

        res
      }

    def genExpandRepeatedArg(argp: Tree): Option[Seq[Val]] = {
      // Given an extern method `def foo(args: Vararg*)`
      argp match {
        // foo(vararg1, ..., varargN) where N > 0
        case MaybeAsInstanceOf(
            WrapArray(MaybeAsInstanceOf(ArrayValue(tpt, elems)))) =>
          val values = mutable.UnrolledBuffer.empty[Val]
          elems.foreach {
            case CVararg(st, argp) =>
              val arg = genExpr(argp)
              values += unboxValue(st, partial = false, arg)
          }
          Some(values)

        // foo(argSeq:_*) - cannot be optimized
        case _ =>
          None
      }
    }
  }
}
