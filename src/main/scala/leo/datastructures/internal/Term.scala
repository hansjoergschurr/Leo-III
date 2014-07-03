package leo.datastructures.internal

import leo.datastructures.Pretty
import scala.language.implicitConversions

/**
 * Abstract interface for generation of various terms that can be
 * displayed in the internal language.
 * Terms are generated by
 *
 * {{{s,t ::= i (bound symbol)
 *       | c (constant symbol)
 *       | λ:tau.s (term abstraction)
 *       | s t (term application)
 *       | Λs (type abstraction)
 *       | s tau (type application)}}}
 *
 * where `c` is some symbol (constant) and `tau` is a type (see `Type`).
 *
 * @author Alexander Steen
 * @since 21.05.2014
 * @note Updated 02.06.2014 Cleaned up method set, lambda terms always have types
 * @note Updated 09.06.2014 Added pattern matcher for terms, added definition expansion
 */
abstract class Term extends Pretty {
  // Predicates on terms
  val isAtom: Boolean
  val isTermApp: Boolean
  val isTermAbs: Boolean
  val isTypeApp: Boolean
  val isTypeAbs: Boolean

  def is(term: Term): Boolean = term == this
  def is(symbol: Signature#Key): Boolean = false

  // Queries on terms
  def ty: Type
  def freeVars: Set[Term]
  def boundVars: Set[Term] = ??? // return the bound vars (that are copies, right?)
  def symbolsOfType(ty: Type) = freeVars.filter(_.ty == ty)
  def topLevelSymbol: Option[Term] = ???
  // Substitutions
  def substitute(what: Term, by: Term): Term
  def substitute(what: List[Term], by: List[Term]): Term = {
    require(what.length == by.length, "Substitution list do not match in length.")
    what.zip(by).foldRight(this)({case ((w,b), t:Term) => t.substitute(w,b)})
  }
  protected[internal] def instantiateBy(by: Type) = instantiate(1,by)
  protected[internal] def instantiate(scope: Int, by: Type): Term

  // Other operations
  /** Returns true iff the term is well-typed. */
  def typeCheck: Boolean

  /** Return the β-nf of the term */
  def betaNormalize: Term
  /** Alias for `betaNormalize` */
  def β_nf: Term = betaNormalize

  /** Right-folding on terms. */
  def foldRight[A](symFunc: Signature#Key => A)
             (boundFunc: (Type, Int) => A)
             (absFunc: (Type, A) => A)
             (appFunc: (A,A) => A)
             (tAbsFunc: A => A)
             (tAppFunc: (A, Type) => A): A

  def expandDefinitions(rep: Int): Term = {
    import Term.{mkAtom, mkBound, mkTermAbs, mkTermApp, mkTypeAbs, mkTypeApp}
    val sig = Signature.get
    def minus = {in: Int => in match {case -1 => -1 case a => a-1}}
    rep match {
      case 0 => this
      case n => {
        val sym: Signature#Key => Term
        = { key =>
          sig.meta(key).defn match {
            case None => mkAtom(key)
            case Some(defn) => defn.expandDefinitions(minus(rep))
          }
        }
        val bound = mkBound(_, _)
        val abs: (Type, Term) => Term
        = { (ty, term) =>
          mkTermAbs(ty, term.expandDefinitions(rep))
        }
        val app: (Term, Term) => Term
        = { (left, right) =>
          mkTermApp(left.expandDefinitions(rep), right.expandDefinitions(rep))
        }
        val tAbs: Term => Term
        = { body =>
          mkTypeAbs(body.expandDefinitions(rep))
        }
        val tApp: (Term, Type) => Term
        = { (body, ty) =>
          mkTypeApp(body.expandDefinitions(rep), ty)
        }
        foldRight(sym)(bound)(abs)(app)(tAbs)(tApp)

      }
    }
  }
  def expandAllDefinitions = expandDefinitions(-1)

  protected[internal] def inc(scopeIndex: Int): Term

  // Syntactic sugar operations
//  /** Creates an (term) application term */
//  def apply(arg: Term): Term = Term.mkTermApp(this,arg)
//  /** Creates an (type) application term */
//  def apply(arg: Type): Term = Term.mkTypeApp(this,arg)
}


object Term {
  def mkAtom = SymbolNode(_)
  def mkBound = BoundNode(_,_)
  def mkTermApp = ApplicationNode(_,_)
  def mkTermApp(func: Term, args: List[Term]): Term = args.foldLeft(func)((arg,f) => mkTermApp(arg,f))
  def mkTermAbs = AbstractionNode(_, _)
  def mkTypeApp = TypeApplicationNode(_,_)
  def mkTypeApp(func: Term, args: List[Type]): Term = args.foldLeft(func)((arg,f) => mkTypeApp(arg,f))
  def mkTypeAbs = TypeAbstractionNode(_)

  // Pretty operators

  /** Creates a new term abstraction with parameter type `hd` and body `body` */
  def \(hd: Type)(body: Term): Term = mkTermAbs(hd, body)
  /** Creates a new term abstraction with parameter type `hd` and body `body`. Pretty variant of `\` */
  def λ(hd: Type)(body: Term): Term = mkTermAbs(hd, body)
  /** Creates a nested term abstraction of the form λ:hd.(λ:h1.(λ:h2.(...(λ:hn,body)..))) for hi ∈ hds */
  def \(hd: Type, hds: Type*)(body: Term): Term = {
    \(hd)(hds.foldRight(body)(\(_)(_)))
  }
  /** Creates a nested term abstraction of the form λ:hd.(λ:h1.(λ:h2.(...(λ:hn,body)..))) for hi ∈ hds */
  def λ(hd: Type, hds: Type*)(body: Term): Term = {
    \(hd)(hds.foldRight(body)(\(_)(_)))
  }

  /** Creates a new type abstracted term  */
  def /\(body: Term): Term = mkTypeAbs(body)
  /** Creates a new type abstracted term. Pretty variant of `/\` */
  def Λ(body: Term): Term = mkTypeAbs(body)

  implicit def intToBoundVar(in: (Int, Type)): Term = mkBound(in._2,in._1)
  implicit def intsToBoundVar(in: (Int, Int)): Term = mkBound(in._2,in._1)
  implicit def keyToAtom(in: Signature#Key): Term = mkAtom(in)
}

/**
 * Pattern for matching bound symbols in terms (i.e. De-Bruijn-Indices). Usage:
 * {{{
 * t match {
 *  case Bound(ty,scope) => println("Matched bound symbol of lambda-scope "
 *                                  + scope.toString + " with type "+ ty.pretty)
 *  case _               => println("something else")
 * }
 * }}}
 */
object Bound {
  def unapply(t: Term): Option[(Type, Int)] = t match {
    case BoundNode(ty,scope) => Some((ty,scope))
    case _ => None
  }
}

/**
 * Pattern for matching constant symbols in terms (i.e. symbols in signature). Usage:
 * {{{
 * t match {
 *  case Symbol(constantKey) => println("Matched constant symbol "+ constantKey.toString)
 *  case _                   => println("something else")
 * }
 * }}}
 */
object Symbol {
  def unapply(t: Term): Option[Signature#Key] = t match {
    case SymbolNode(k) => Some(k)
    case _ => None
  }
}

/**
 * Pattern for matching (term) applications in terms (i.e. terms of form `(s t)`). Usage:
 * {{{
 * t match {
 *  case s @@@ t => println("Matched application. Left: " + s.pretty
 *                                            + " Right: " + t.pretty)
 *  case _       => println("something else")
 * }
 * }}}
 */
object @@@ extends HOLBinaryConnective {
  val key = Integer.MIN_VALUE // just for fun!
  override def unapply(t: Term): Option[(Term,Term)] = t match {
    case ApplicationNode(l,r) => Some((l,r))
    case _ => None
  }
  override def apply(left: Term, right: Term): Term = Term.mkTermApp(left,right)
}

/**
 * Pattern for matching type applications in terms (i.e. terms of form `(s ty)` where `ty` is a type). Usage:
 * {{{
 * t match {
 *  case s :::: ty => println("Matched type application. Left: " + s.pretty
 *                                                  + " Right: " + ty.pretty)
 *  case _         => println("something else")
 * }
 * }}}
 */
object @@@@ {
  def unapply(t: Term): Option[(Term,Type)] = t match {
    case TypeApplicationNode(l,r) => Some((l,r))
    case _ => None
  }
}

/**
 * Pattern for matching (term) abstractions in terms (i.e. terms of form `(\(ty)(s))` where `ty` is a type). Usage:
 * {{{
 * t match {
 *  case ty :::> s => println("Matched abstraction. Type of parameter: " + ty.pretty
 *                                                           + " Body: " + s.pretty)
 *  case _         => println("something else")
 * }
 * }}}
 */
object :::> extends Function2[Type, Term, Term] {
  def unapply(t: Term): Option[(Type,Term)] = t match {
    case AbstractionNode(ty,body) => Some((ty,body))
    case _ => None
  }

  /** Construct abstraction λty.body */
  override def apply(ty: Type, body: Term): Term = Term.mkTermAbs(ty, body)
}

/**
 * Pattern for matching (type) abstractions in terms (i.e. terms of form `/\(s)`). Usage:
 * {{{
 * t match {
 *  case TypeLambda(s) => println("Matched type abstraction. Body: " + s.pretty)
 *  case _             => println("something else")
 * }
 * }}}
 */
object TypeLambda {
  def unapply(t: Term): Option[Term] = t match {
    case TypeAbstractionNode(body) => Some(body)
    case _ => None
  }
}

