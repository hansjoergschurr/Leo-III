package leo.modules.special_processing

import leo.datastructures.{AnnotatedClause, Literal, Signature, Term}
import leo.modules.HOLSignature.o
import leo.datastructures.Term._

/**
  * Created by Hans-Jörg Schurr on 3/7/17.
  */
object UniversalReduction {

  private def isBooleanVar(l: Literal) : Boolean = {
    !l.equational && l.left.isVariable && l.left.ty == o
  }

  private def allBooleanVars(t: Term) : Set[Term] = t match {
    case Bound(_, _) => Set.empty
    case t1 ∙ t2 => allBooleanVars(t1).union(allBooleanVars(t2))
    case Symbol(t) => Set(t)
  }

  /**
    * This method removes universally quantified variables from clauses. Such variables can be removed, if
    * they don't appear only as individual literals, and nowhere else.
    *
    * @param clauses the matrix
    * @return new set of clauses
    */
  def findUnitClauses(clauses : Set[AnnotatedClause])(implicit sig: Signature) : Set[AnnotatedClause] = {
    clauses.map { c =>
      val uniVars = Set(for (l <- c.cl.lits if isBooleanVar(l)) yield l)

      c
    }
    clauses
  }
}
