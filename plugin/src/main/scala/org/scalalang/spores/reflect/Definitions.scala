package org.scalalang.spores
package reflect

trait Definitions {
  self: Enrichments =>

  import global._
  import rootMirror._
  import definitions._
  import scala.reflect.internal.Flags._
  import scala.reflect.internal.util.Statistics
  import scala.reflect.internal.TypesStats._
  import scala.language.reflectiveCalls

  object sporeDefinitions {
    lazy val SerializableTpe = SerializableClass.tpe

    /** The single abstract method declared by type `tp` (or `NoSymbol` if it cannot be found).
     *
     * The method must be monomorphic and have exactly one parameter list.
     * The class defining the method is a supertype of `tp` that
     * has a public no-arg primary constructor.
     */
    def samOf(tp: Type): Symbol = {
      val ctor = tp.typeSymbol.primaryConstructor
      // if it has a constructor, must be public and must not take any arguments (not even implicitly)
      if (ctor == NoSymbol || (!ctor.isOverloaded && ctor.isPublic && ctor.info.params.isEmpty && ctor.info.paramSectionCount <= 1)) {
        // find the single abstract member, if there is one
        val deferredMembers = findPublicMethods(tp).filter(mem => mem.isDeferred && !isUniversalMember(mem))

        // if there is only one, it's monomorphic and has a single argument list
        if (deferredMembers.size == 1 &&
            deferredMembers.head.typeParams.isEmpty &&
            deferredMembers.head.info.paramSectionCount == 1)
          deferredMembers.head
        else NoSymbol
      } else NoSymbol
    }

    /** Is this symbol a member of Object or Any? */
    def isUniversalMember(sym: Symbol) = ObjectClass isSubClass sym.owner

    def findPublicMethods(tp: Type): Scope = {
      // don't go out requiring DEFERRED members, as you will get them even if there's a concrete override:
      //    scala> abstract class X { def m: Int }
      //    scala> class Y extends X { def m: Int = 1}
      //    scala> typeOf[Y].deferredMembers
      //    Scopes(method m, method getClass)
      //
      //    scala> typeOf[Y].members.filter(_.isDeferred)
      //    Scopes()
      // must filter out "universal" members (getClass is deferred for some reason)
      val excludedFlags = BridgeAndPrivateFlags
      val requiredFlags = METHOD

      def findMembersInternal: Scope = {
        var members: Scope = null
        if (Statistics.canEnable) Statistics.incCounter(findMembersCount)
        val start = if (Statistics.canEnable) Statistics.pushTimer(typeOpsStack, findMembersNanos) else null

        //Console.println("find member " + name.decode + " in " + this + ":" + this.baseClasses)//DEBUG
        var required = requiredFlags
        var excluded = excludedFlags | DEFERRED
        var retryForDeferred = true
        var self: Type = null
        while (retryForDeferred) {
          retryForDeferred = false
          val bcs0 = tp.baseClasses
          var bcs = bcs0
          while (!bcs.isEmpty) {
            val decls = bcs.head.info.decls
            var entry = decls.asInstanceOf[{ var elems: ScopeEntry }].elems
            while (entry ne null) {
              val sym = entry.sym
              val flags = sym.flags
              if ((flags & required) == required) {
                val excl = flags & excluded
                if (excl == 0L &&
                    (// omit PRIVATE LOCALS unless selector class is contained in class owning the def.
                     (bcs eq bcs0) ||
                     (flags & PrivateLocal) != PrivateLocal ||
                     (bcs0.head.hasTransOwner(bcs.head)))) {
                  if (members eq null) members = newFindMemberScope
                  var others: ScopeEntry = members.lookupEntry(sym.name)
                  var symtpe: Type = null
                  while ((others ne null) && {
                           val other = others.sym
                           (other ne sym) &&
                           ((other.owner eq sym.owner) ||
                            (flags & PRIVATE) != 0 || {
                               if (self eq null) self = narrowForFindMember(tp)
                               if (symtpe eq null) symtpe = self.memberType(sym)
                               !(self.memberType(other) matches symtpe)
                            })}) {
                    others = members lookupNextEntry others
                  }
                  if (others eq null) members enter sym
                } else if (excl == DEFERRED) {
                  retryForDeferred = (excludedFlags & DEFERRED) == 0
                }
              }
              entry = entry.next
            } // while (entry ne null)
            // excluded = excluded | LOCAL
            bcs = bcs.tail
          } // while (!bcs.isEmpty)
          required |= DEFERRED
          excluded &= ~(DEFERRED.toLong)
        } // while (retryForDeferred)
        if (Statistics.canEnable) Statistics.popTimer(typeOpsStack, start)
        if (members eq null) EmptyScope else members
      }

      if (tp.isGround) findMembersInternal
      else suspendingTypeVars(typeVarsInType(tp))(findMembersInternal)
    }

    def newFindMemberScope: Scope = new Scope() {
      override def sorted = {
        val members = toList
        val owners = members.map(_.owner).distinct
        val grouped = members groupBy (_.owner)
        owners.flatMap(owner => grouped(owner).reverse)
      }
    }

    def narrowForFindMember(tp: Type): Type = {
      val w = tp.widen
      // Only narrow on widened type when we have to -- narrow is expensive unless the target is a singleton type.
      if ((tp ne w) && containsExistential(w)) w.narrow
      else tp.narrow
    }

    // If this type contains type variables, put them to sleep for a while.
    // Don't just wipe them out by replacing them by the corresponding type
    // parameter, as that messes up (e.g.) type variables in type refinements.
    // Without this, the matchesType call would lead to type variables on both
    // sides of a subtyping/equality judgement, which can lead to recursive types
    // being constructed. See pos/t0851 for a situation where this happens.
    def suspendingTypeVars[T](tvs: List[TypeVar])(op: => T): T = {
      val saved = tvs map (_.asInstanceOf[{ var suspended: Boolean }].suspended)
      tvs foreach (_.asInstanceOf[{ var suspended: Boolean }].suspended = true)

      try op
      finally foreach2(tvs, saved)(_.asInstanceOf[{ var suspended: Boolean }].suspended = _)
    }

    val typeIsSubTypeOfSerializable = (tp: Type) => tp <:< SerializableClass.tpe
  }
}
