package leo.datastructures

import leo.modules.output.Output


/////////////////////////////////////////////
// Collection of potentially globally used
// markers/properties.
/////////////////////////////////////////////

/**
 * Formula roles as described by TPTP.
 *
 * @author Alexander Steen
 * @since 11.11.2014
 * @see [[http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html]]
 */
sealed abstract class Role extends Pretty

/**
 * `Role_Axiom`s are accepted, without proof. There is no guarantee that the
 * axioms of a problem are consistent.
 */
case object Role_Axiom extends Role {
  final val pretty = "axiom"
}

/**
 * `Role_Definition`s are intended to define symbols. They are either universally
 * quantified equations, or universally quantified equivalences with an
 * atomic lefthand side.
 */
case object Role_Definition extends Role {
  final val pretty = "definition"
}

/**
 * `Role_Assumption`s can be used like axioms, but must be discharged before a
 * derivation is complete.
 */
case object Role_Assumption extends Role {
  final val pretty = "assumption"
}

/**
 * `Role_Conjecture`s are to be proven from the "axiom"(-like) formulae. A problem
 * is solved only when all "conjecture"s are proven.
 */
case object Role_Conjecture extends Role {
  final val pretty = "conjecture"
}

/**
 * `Negated_Conjecture`s are formed from negation of a "conjecture" (usually
 * in a FOF to CNF conversion).
 */
case object Role_NegConjecture extends Role {
  final val pretty = "negated_conjecture"
}

/**
 * `Role_Type`s define the type globally for one symbol.
 */
case object Role_Type extends Role {
  final val pretty = "type"
}

/**
 * `Role_Plain`s have no specified user semantics.
 */
case object Role_Plain extends Role {
  final val pretty = "plain"
}

/**
 * `Role_Unknown`s are considered an error.
 */
case object Role_Unknown extends Role {
  final val pretty = "unknown"
}

object Role {
  def apply(role: String): Role = role.trim match {
    case "axiom" => Role_Axiom
    case "hypothesis" => Role_Axiom // Note: Implicit mapping to axiom
    case "definition" => Role_Definition
    case "assumption" => Role_Assumption
    case "lemma" => Role_Axiom // Note: Implicit mapping to axiom
    case "theorem" => Role_Axiom // Note: Implicit mapping to axiom
    case "conjecture" => Role_Conjecture
    case "negated_conjecture" => Role_NegConjecture
    case "plain" => Role_Plain
    case "type" => Role_Type
    case "unknown" => Role_Unknown
    case _ => Role_Unknown // Note: fi_* roles are not handled at the moment
  }
}


//////////////////////////////////////////////
//////////////////////////////////////////////


abstract sealed class ClauseOrigin extends Ordered[ClauseOrigin] {
  protected[ClauseOrigin] def priority: Int

  def compare(that: ClauseOrigin) = this.priority - that.priority
}
case object FromAxiom extends ClauseOrigin { val priority = 3 }
case object FromConjecture extends ClauseOrigin { val priority = 2 }
case object Derived extends ClauseOrigin { val priority = 1 }




trait ClauseProxy extends Pretty {
  def id: Long
  def cl: Clause
  def role: Role
  def annotation: ClauseAnnotation
  def properties: ClauseAnnotation.ClauseProp

  override def pretty: String = s"[$id]:\t${cl.pretty}\t(${annotation.pretty}) (Flags: ${ClauseAnnotation.prettyProp(properties)})"
}

case class AnnotatedClause(id: Long, cl: Clause, role: Role, annotation: ClauseAnnotation,
                           var properties: ClauseAnnotation.ClauseProp) extends ClauseProxy with Ordered[AnnotatedClause] {
  override def equals(o: Any): Boolean = o match {
    case cw: ClauseProxy => cw.cl == cl // TODO: Does this make sense?
    case _ => false
  }
  import leo.Configuration
  override def compare(that: AnnotatedClause) = Configuration.CLAUSE_ORDERING.compare(this.cl, that.cl)
  override def hashCode(): Int = cl.hashCode()  // TODO: Does this make sense?

  var additionalInformation: Option[AnyRef] = None
}

object AnnotatedClause {
  private var counter: Long = 0

  def apply(cl: Clause, r: Role, annotation: ClauseAnnotation, propFlag: ClauseAnnotation.ClauseProp): AnnotatedClause = {
    counter += 1
    AnnotatedClause(counter, cl, r, annotation, propFlag)
  }

  def apply(cl: Clause, annotation: ClauseAnnotation, propFlag: ClauseAnnotation.ClauseProp = ClauseAnnotation.PropNoProp): AnnotatedClause =
    apply(cl, Role_Plain, annotation, propFlag)
}

abstract sealed class ClauseAnnotation extends Pretty {
  def fromRule: Option[leo.modules.calculus.CalculusRule]
}

object ClauseAnnotation {
  case class InferredFrom[A <: ClauseProxy](rule: leo.modules.calculus.CalculusRule, cws: Set[(A, Output)]) extends ClauseAnnotation {
    def pretty: String = s"inference(${rule.name},[${rule.inferenceStatus.fold("")("status(" + _.pretty.toLowerCase + ")")}],[${
      cws.map { case (cw, add) => if (add == null) {
        cw.id
      } else {
        cw.id  + ":[" + add.apply + "]"
      }
      }.mkString(",")
    }])"

    val fromRule = Some(rule)
  }
  object InferredFrom {
    def apply[A <: ClauseProxy](rule: leo.modules.calculus.CalculusRule, cs: Set[A]): ClauseAnnotation =
      InferredFrom(rule, cs.map((_, null.asInstanceOf[Output])))

    def apply[A <: ClauseProxy](rule: leo.modules.calculus.CalculusRule, c: A): ClauseAnnotation =
      InferredFrom(rule, Set((c,null.asInstanceOf[Output])))
  }

  case object NoAnnotation extends ClauseAnnotation {
    val pretty: String = ""
    val fromRule = None
  }
  case class FromFile(fileName: String, formulaName: String) extends ClauseAnnotation {
    def pretty = s"file('$fileName',$formulaName)"
    val fromRule = None
  }

  type ClauseProp = Int
  final val PropNoProp: ClauseProp = 0
  final val PropUnified: ClauseProp = 1
  final val PropBoolExt: ClauseProp = 2
  final val PropSOS: ClauseProp = 4
  final val PropNeedsUnification: ClauseProp = 8

  final def prettyProp(prop: ClauseProp): String = {
    val sb = new StringBuilder
    if (isPropSet(PropUnified, prop)) sb.append(" U ")
    if (isPropSet(PropBoolExt, prop)) sb.append(" BE ")
    if (isPropSet(PropSOS, prop)) sb.append(" SOS ")
    if (isPropSet(PropNeedsUnification, prop)) sb.append(" NU ")
    sb.toString()
  }
}


//////////////////////////////////////////////
//////////////////////////////////////////////


abstract sealed class Indexing
case object INDEXED extends Indexing
case object PLAIN extends Indexing


//////////////////////////////////////////////
//////////////////////////////////////////////


abstract sealed class Locality
case object GLOBAL extends Locality
case object LOCAL extends Locality


//////////////////////////////////////////////
//////////////////////////////////////////////


/**
 * Marker type for the 'language level' of terms.
 * A Term is flagged `PROPOSITIONAL` iff it is a propositional formula,
 * analogously for `FIRSTORDER` and `HIGHERORDER`.
 *
 * @author Alexander Steen
 */
sealed abstract class LangOrder extends Ordered[LangOrder]

case object Lang_Prop extends LangOrder {
  def compare(that: LangOrder) = that match {
    case Lang_Prop => 0
    case _ => -1
  }
}

case object Lang_FO extends LangOrder {
  def compare(that: LangOrder) = that match {
    case Lang_Prop => 1
    case Lang_FO => 0
    case Lang_ManySortedFO | Lang_HO => -1
  }
}

case object Lang_ManySortedFO extends LangOrder {
  def compare(that: LangOrder) = that match {
    case Lang_Prop | Lang_FO => 1
    case Lang_ManySortedFO => 0
    case Lang_HO => -1
  }
}

case object Lang_HO extends LangOrder {
  def compare(that: LangOrder) = that match {
    case Lang_HO => 0
    case _ => 1
  }
}


//////////////////////////////////////////////
//////////////////////////////////////////////
