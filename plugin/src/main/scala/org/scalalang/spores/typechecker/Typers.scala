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

      // parents.head may not be fully defined, but it will be before we type the ClassDef
      val parents  = parentTps map TypeTree
      val templ    = Template(parents, emptyValDef, NoMods, ListOfNil, ListOfNil, List(samDef), pos.focus)

      // Need to type method before classdef to fully determine samClassTp.
      // As it determines a parent type for the class, we don't want to type check `block` (see below)
      // all at once (which would be ideal otherwise).
      // That would propagate the wildcard to the class's self type, parent types,...
      // Thus, we set up a minimal dummy context and ask for the method's final result type
      val samClassTpFullyDefined =
        if (samDefTp ne NoType) samClassTp
        else {
          // temporary symbol to set up a minimal context for typing the DefDef for the sam so we can determine the result type
          val anonClass = context.owner newAnonymousFunctionClass pos
          anonClass setInfo ClassInfoType(parentTps, newScope, anonClass)

          // this creates a symbol for samDef with a type completer
          // and enters the symbol in the temporary scope (anonClass.info.decls)
          enterSym(context.make(templ, anonClass, anonClass.info.decls), samDef)

          // so, what's the actual type? (this will run the type completer)
          val bodyTp = samDef.symbol.info.finalResultType

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


    private def typedFunction(fun: Function, mode: Int, pt: Type): Tree = {
      val numVparams = fun.vparams.length
      val FunctionSymbol = FunctionClass(numVparams)

      /* Matches a subtype of FunctionN where N is the expected number of parameters.
       */
      object FunctionType {
        def unapply(tp: Type): Option[(List[Type], Type)] = {
          tp baseType FunctionSymbol match {
            case TypeRef(_, FunctionSymbol, args :+ res) => Some((args, res))
            case _ => None
          }
        }
      }

      /* Matches a type that has a SAM with the expected number of parameters,
       * excluding the Function type corresponding to the expected number of parameters.
       *
       * For mismatching arity, we continue type checking with unknown parameter types,
       * as there may still be an implicit conversion to a function of the right arity (pos/t0438)
       */
      object SAMType {
        def unapply(tp: Type): Option[(Symbol, List[Type], Type)] =
          // don't give FunctionN the SAM treatment (yet)
          if (!(tp.isWildcard || tp.isError) && tp.typeSymbol != FunctionSymbol) {
            val sam = samOf(tp)

            if (sam != NoSymbol && sameLength(sam.info.params, fun.vparams)) {
              val samInfo = tp memberInfo sam
              Some((sam, samInfo.paramTypes, samInfo.resultType))
            } else None
          } else None
      }

      /* The SAM case comes first so that this works:
       *   abstract class MyFun extends (Int => Int)
       *   (a => a): MyFun
       *
       * However, `(a => a): Int => Int` should not get the sam treatment.
       *
       * Note that SAMType only matches when the arity of the sam corresponds to the arity of the function.
       */
      val (funSym, argpts, respt) =
        pt match {
          case SAMType(mem, args, res) => (mem, args, res)
          case FunctionType(args, res) => (FunctionSymbol, args, res)
          case _                       => (FunctionSymbol, fun.vparams map (_ => NoType), WildcardType)
        }

      // max arity restriction does not apply to SAM
      if (funSym == FunctionSymbol && numVparams > definitions.MaxFunctionArity)
        return MaxFunctionArityError(fun)

      val expectedArity =
        if (pt.typeSymbol == PartialFunctionClass) 1
        else FunctionClass indexOf pt.typeSymbol match {
          // Expected type's symbol was not a FunctionN -- maybe it was a subtype of FunctionN or a SAM type?
          // samOf works both for subtypes of FunctionN and generalized SAM types
          case -1    =>
            val sam = samOf(pt)
            if (sam != NoSymbol) sam.info.params.length
            else -1
          case arity => arity
        }

      val parameterTypesKnown = !fun.vparams.exists(_.tpt.isEmpty)

      // proceed if: arity as expected|| no expected arity || all parameter types are known
      if (numVparams == expectedArity || expectedArity < 0 || parameterTypesKnown) {
        if (!parameterTypesKnown)
          foreach2(fun.vparams, argpts) { (vparam, argpt) =>
            if (vparam.tpt.isEmpty) {
              vparam.tpt.tpe =
                if (isFullyDefined(argpt)) argpt
                else {
                  fun match {
                    case etaExpansion(vparams, fn, args) =>
                      silent(_.typed(fn, forFunMode(mode), pt)) filter (_ => context.undetparams.isEmpty) map { fn1 =>
                          // if context,undetparams is not empty, the function was polymorphic,
                          // so we need the missing arguments to infer its type. See #871
                          //println("typing eta "+fun+":"+fn1.tpe+"/"+context.undetparams)
                          val ftpe = normalize(fn1.tpe) baseType FunctionClass(numVparams)
                          if (isFunctionType(ftpe) && isFullyDefined(ftpe))
                            return typedFunction(fun, mode, ftpe)
                      }
                    case _ =>
                  }
                  MissingParameterTypeError(fun, vparam, pt)
                  ErrorType
                }
              if (!vparam.tpt.pos.isDefined) vparam.tpt setPos vparam.pos.focus
            }
          }

        fun.body match {
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
          // to `new $pt { def ${funSym.name}($p1: $T1, ..., $pN: $TN): $resTp = $body }`
          case _ if funSym.isMethod => // a sam type
            val outerTyper = newTyper(context.outer)
            outerTyper.synthesizeSAMFunction(funSym, fun, respt, pt, mode)

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
            val funtpe  = appliedType(funSym, formals :+ restpe: _*)

            treeCopy.Function(fun, vparams, body1) setType funtpe
        }
      } else WrongNumberOfParametersError(fun, expectedArity)
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
