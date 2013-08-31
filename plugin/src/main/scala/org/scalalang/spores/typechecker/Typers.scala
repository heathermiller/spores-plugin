package org.scalalang.spores
package typechecker

trait Typers {
  self: Analyzer =>

  import global.{typeIsSubTypeOfSerializable => _, _}
  import definitions._
  import sporeDefinitions._
  import scala.reflect.internal.Flags._
  import scala.collection.mutable.ListBuffer
  import scala.tools.nsc.ListOfNil

  trait SporeTyper extends Typer with SporeTyperContextErrors {
    import TyperErrorGen.{WrongNumberOfParametersError => _, _}
    import SporeTyperErrorGen._
    import infer._

    def isFullyDefined(tp: Type): Boolean = tp match {
      case WildcardType | BoundedWildcardType(_) | NoType =>
        false
      case NoPrefix | ThisType(_) | ConstantType(_) =>
        true
      case TypeRef(pre, sym, args) =>
        isFullyDefined(pre) && (args forall isFullyDefined)
      case SingleType(pre, sym) =>
        isFullyDefined(pre)
      case RefinedType(ts, decls) =>
        ts forall isFullyDefined
      case TypeVar(origin, constr) if (constr.inst == NoType) =>
        false
      case _ =>
        try {
          self.instantiate(tp); true
        } catch {
          case ex: NoInstance => false
        }
    }

    def newPatternMatching = opt.virtPatmat && !forInteractive

    implicit class RichSilentResult[T](sr: SilentResult[T]) {
      @inline final def fold[U](none: => U)(f: T => U): U = sr match {
        case SilentResultValue(value) => f(value)
        case _                        => none
      }
      @inline final def map[U](f: T => U): SilentResult[U] = sr match {
        case SilentResultValue(value) => SilentResultValue(f(value))
        case x: SilentTypeError       => x
      }
      @inline final def flatMap[U](f: T => SilentResult[U]): SilentResult[U] = sr match {
        case SilentResultValue(value) => f(value)
        case x: SilentTypeError       => x
      }
      @inline final def filter(p: T => Boolean): SilentResult[T] = sr match {
        case SilentResultValue(value) if !p(value) => NoSilentResult
        case _                                     => sr
      }
      @inline final def orElse[T1 >: T](f: AbsTypeError => T1): T1 = sr match {
        case SilentResultValue(value) => value
        case SilentTypeError(err)     => f(err)
      }
    }

    lazy val NoSilentResult = SilentTypeError(TypeErrorWrapper(new TypeError(NoPosition, "No SilentResult available.")))

    /** Synthesize and type check the implementation of a type with a Single Abstract Method
     *
     *  Assuming:
     *    - fun == `(p1: T1, ..., pN: TN) => body`
     *    - resTp is the type of body typed while expecting resPt (with pi: Ti in scope)
     *
     *  We synthesize:
     *
     *  new $samClassTp {
     *    def ${sam.name}($p1: $T1, ..., $pN: $TN): $resTp = $body
     *  }
     *
     * The method will be referred to as `sam`.
     *
     * TODO: it would be nicer to generate the tree specified above at once and type it as a whole,
     * there are two gotchas:
     *    - we don't know typedBody.tpe until we've typed the body (unless it was specified),
     *       - if we typed the body in isolation first, you'd know its result type, but would have to re-jig the owner structure
     *       - could we use a type variable for the result type and backpatch it?
     *    - occurrences of `this` in `cases` or `sel` must resolve to the this of the class originally enclosing the function,
     *      not of the anonymous partial function subclass
     */
    def synthesizeSAMFunction(sam: Symbol, fun: Function, resPt: Type, samClassTp: Type, mode: Int): Tree = {
      // assert(fun.vparams forall (vp => isFullyDefined(vp.tpt.tpe))) -- by construction, as we take them from sam's info
      val pos = fun.pos

      val serializableParentAddendum =
        if (typeIsSubTypeOfSerializable(samClassTp)) Nil
        else List(SerializableTpe)

      val parentTps = samClassTp :: serializableParentAddendum

      // if the expected sam type is fully defined, use it for the method's result type
      // otherwise, NoType, so that type inference will determine the method's result type
      // resPt is syntactically contained in samClassTp, so if the latter is fully defined, so is the former
      // ultimately, we want to fully define samClassTp as it is used as the superclass of our anonymous class
      val samDefTp = if (isFullyDefined(samClassTp)) resPt else NoType

      // `final override def ${sam.name}($p1: $T1, ..., $pN: $TN): $resPt = $body`
      val samDef =
        DefDef(Modifiers(FINAL | OVERRIDE),
          sam.name.toTermName,
          Nil,
          List(fun.vparams),
          TypeTree(samDefTp) setPos pos.focus,
          fun.body)

      // Need to type method before classdef to fully determine samClassTp.
      // As it determines a parent type for the class, we don't want to type check `block` (see below)
      // all at once (which would be ideal otherwise).
      // That would propagate the wildcard to the class's self type, parent types,...
      // Thus, we set up a minimal dummy context and ask for the method's final result type

      // temporary symbol to set up a minimal context for typing the DefDef for the sam so we can determine the result type
      // val anonClass = context.owner newAnonymousFunctionClass pos
      // anonClass setInfo ClassInfoType(parentTps, newScope, anonClass)

      // Use a temporary scope that's nested in the current scope.
      // Don't use `anonClass.info.decls`, as the class's members are not in scope in the function's body!
      // Once synthesis is over, the method's symbol is entered in the class's scope (where it belongs) using:
      // `classDef.symbol.info.decls enter samDef.symbol`

      // This creates a symbol for samDef with a type completer that'll be triggered below.
      // The symbol is entered in the temporary scope (as it can't be in the sam class's scope).
      println("context: "+ context)
      enterSym(context.makeNewScope(context.tree, context.owner), samDef)

      // so, what's the actual type? (this will run the type completer)
      val bodyTp = samDef.symbol.info.finalResultType

      // parents.head may not be fully defined, but it will be before we type the ClassDef
      val parents  = parentTps map TypeTree

      val samClassTpFullyDefined =
        if (samDefTp ne NoType) samClassTp
        else  {
          // infer samClassTp's type args based on bodyTp
          // TODO: this doesn't consider implicit args on `samClass.primaryConstructor`...
          val fullyDefined = {
            val samClass  = samClassTp.typeSymbol
            // the unknowns
            val tparams   = samClass.typeParams
            // ... as typevars
            val tvars     = tparams map freshVar

            // we're trying to fully define the type arguments for this type constructor
            val samTyCon  = samClass.typeConstructor

            // the declared type, which refers to the (potentially) unknown type params
            // so that we can infer them by comparing it to body's the actual type
            val samResTp  = sam.info.resultType

            // constrain typevars
            // 1. we compare to the samClassTp, to propagate any already determined type parameters
            samClassTp =:= appliedType(samTyCon, tvars)

            // 2. make sure the body's actual type conforms to the expected type
            // as specified by the method's return type (in terms of the typevars that represent the sam's class's type params)
            bodyTp     <:< samResTp.substituteTypes(tparams, tvars)

            // solve constraints tracked by tvars
            val targs = solvedTypes(tvars, tparams, tparams map varianceInType(samResTp), upper = false, lubDepth(samResTp :: bodyTp :: Nil))

            // a fully defined samClassTp
            appliedType(samTyCon, targs)
          }

          // make first parent (samClassTp) fully defined --> ready to typecheck classdef (below)!
          parents.head setType fullyDefined
          fullyDefined
        }

      val templ    = Template(parents, emptyValDef, NoMods, ListOfNil, ListOfNil, List(samDef), pos.focus)
      // type checking the whole block, so that everything is packaged together nicely and we don't have to create any symbols by hand
      val classDef = ClassDef(Modifiers(FINAL), tpnme.ANON_FUN_NAME, Nil, templ)
      val block =
        typedPos(pos, mode, samClassTpFullyDefined) {
          Block(classDef, Apply(Select(New(Ident(tpnme.ANON_FUN_NAME)), nme.CONSTRUCTOR), Nil))
        }

      // fix up owner structure
      if (samDefTp eq NoType) {
        // the anonClass owner was only temporary, we just wanted to figure out the type of samDef's body
        samDef.symbol.owner = classDef.symbol

        // samDef already had a symbol when typing `block` above, so namer.enterSym didn't enter it when typing `templ`
        // TODO: why not enter trees with a symbol?
        classDef.symbol.info.decls enter samDef.symbol
      }

      classDef.symbol addAnnotation AnnotationInfo(SerialVersionUIDAttr.tpe, List(Literal(Constant(0))), List())
      block
    }

    private def typedFunction(fun: Function, mode: Int, pt: Type, unrollEtaExpansion: Boolean = true): Tree = {
      val numVparams = fun.vparams.length
      val ExpectedFunctionSymbol = if (numVparams <= MaxFunctionArity) FunctionClass(numVparams) else NoSymbol

      /** Matches a type that has a SAM with the expected number of parameters (numVparams).
       *
       * For mismatching arity, we continue type checking with unknown parameter types,
       * as there may still be an implicit conversion to a function of the right arity (pos/t0438)
       */

      /* The SAM case comes first so that this works:
       *   abstract class MyFun extends (Int => Int)
       *   (a => a): MyFun
       *
       * However, `(a => a): Int => Int` should not get the sam treatment.
       *
       * Note that SAMType only matches when the arity of the sam corresponds to the arity of the function.
       */
      // Expected type's symbol was not a FunctionN -- maybe it was a subtype of FunctionN or a SAM type?
      // samOf works both for subtypes of FunctionN and generalized SAM types


      val (sam, argpts, respt, expectedArity) =
        if (pt.typeSymbol == PartialFunctionClass) {
          val pfargs = (pt baseType PartialFunctionClass).typeArgs
          (NoSymbol, pfargs.init, pfargs.last, 1)
        } else
          samOf(pt) match {
            case sam if sam.exists && sameLength(sam.info.params, fun.vparams) =>
              val samInfo = pt memberInfo sam
              // println(s"pt: $pt / sam: $sam / samInfo: $samInfo")
              (sam, samInfo.paramTypes, samInfo.resultType, numVparams) // arity is checked by sameLength call above
            case _  =>
              val sam = ExpectedFunctionSymbol.info nonPrivateMember nme.apply
              val paramTypesUnknown = fun.vparams map (_ => NoType)
              (sam, paramTypesUnknown, WildcardType, FunctionClass indexOf pt.typeSymbol)
          }

      val unknownParamTypes = fun.vparams.exists(_.tpt.isEmpty)
      val missingParamTypes = new ListBuffer[ValDef]

      // `fun.vparams.length > MaxFunctionArity`
      if (!sam.exists) MaxFunctionArityError(fun)
      // arity mismatch and need to infer parameter types
      else if (unknownParamTypes) {
        if (numVparams != expectedArity) WrongNumberOfParametersError(fun, expectedArity)
        else
          foreach2(fun.vparams, argpts) { case (vparam, argpt) if vparam.tpt.isEmpty =>
            if (isFullyDefined(argpt)) vparam.tpt setType argpt
            else {
              missingParamTypes += vparam
              setError(vparam.tpt)
            }
            if (!vparam.tpt.pos.isDefined) vparam.tpt setPos vparam.pos.focus
          }
      }

      // one last chance: try to infer missing parameter types by undoing eta-expansion and typing the eta-expanded function directly
      if (unrollEtaExpansion && missingParamTypes.nonEmpty) {
        (fun match {
          // case Function(List(valDef1, ..., valDefN), Apply(fn, List(Ident(arg1), ..., Ident(argN)))) if forall valDefI.name == argI =>
          case etaExpansion(_, fn, _) =>
            silent(_.typed(fn, forFunMode(mode), pt)) flatMap { origFun =>
              // if context.undetparams is not empty, the function was polymorphic,
              // so we need the missing arguments to infer its type. See #871
              if (context.undetparams.isEmpty) {
                //println("typing eta "+fun+":"+fn1.tpe+"/"+context.undetparams)
                val retryPt = normalize(origFun.tpe)
                if (isFullyDefined(retryPt))
                  SilentResultValue(typedFunction(fun, mode, retryPt, unrollEtaExpansion = false))
                else NoSilentResult
              } else NoSilentResult
            }
          case _ => NoSilentResult
        }) orElse { error =>
          missingParamTypes foreach (MissingParameterTypeError(fun, _, pt))
          setError(fun)
          fun
        }
      }
      else fun.body match {
        // translate `x => x match { <cases> }` : PartialFunction to
        // `new PartialFunction { def applyOrElse(x, default) = x match { <cases> } def isDefinedAt(x) = ... }`
        case Match(sel, cases) if (sel ne EmptyTree) && newPatternMatching && (pt.typeSymbol == PartialFunctionClass) =>
          // go to outer context -- must discard the context that was created for the Function since we're discarding the function
          // thus, its symbol, which serves as the current context.owner, is not the right owner
          // you won't know you're using the wrong owner until lambda lift crashes (unless you know better than to use the wrong owner)
          val outerTyper = newTyper(context.outer)
          val p = fun.vparams.head
          if (p.tpt.tpe == null) p.tpt setType outerTyper.typedType(p.tpt).tpe

          outerTyper.synthesizePartialFunction(p.name, p.pos, fun.body, mode, pt)

        // translate `(p1: T1, ..., pN: TN) => body`
        // to `new $pt { def ${sam.name}($p1: $T1, ..., $pN: $TN): $resTp = $body }`
        // a true sam type (the special case for Function below is not strictly necessary)
        case _ if sam.owner ne ExpectedFunctionSymbol =>
          val outerTyper = newTyper(context.outer)
          outerTyper.synthesizeSAMFunction(sam, fun, respt, pt, mode)

        // regular Function
        case _ =>
          val vparamSyms = fun.vparams map { vparam =>
            enterSym(context, vparam)
            if (context.retyping) context.scope enter vparam.symbol
            vparam.symbol
          }
          val vparams = fun.vparams mapConserve typedValDef
          val formals = vparamSyms map (_.tpe)
          val body1   = typed(fun.body, respt)
          val restpe  = packedType(body1, fun.symbol).deconst.resultType
          val funtpe  = appliedType(sam.owner, formals :+ restpe: _*)

          treeCopy.Function(fun, vparams, body1) setType funtpe
      }
    }

    override def typed1(tree: Tree, mode: Int, pt: Type): Tree = {
      def typedFunction(fun: Function) = {
        if (fun.symbol == NoSymbol)
          fun.symbol = context.owner.newAnonymousFunctionValue(fun.pos)

        typerWithLocalContext(context.makeNewScope(fun, fun.symbol))(_.asInstanceOf[SporeTyper].typedFunction(fun, mode, pt))
      }

      val sym: Symbol = tree.symbol
      if ((sym ne null) && (sym ne NoSymbol)) sym.initialize

      tree match {
        case tree: Function  => typedFunction(tree)
        case _               => super.typed1(tree, mode, pt)
      }
    }
  }
}
