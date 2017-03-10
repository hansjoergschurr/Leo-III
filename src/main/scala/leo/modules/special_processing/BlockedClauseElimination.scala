package leo.modules.special_processing

import leo.datastructures.{AnnotatedClause, Signature}
import leo.modules.calculus.CalculusRule
import leo.modules.output.SZS_EquiSatisfiable

/**
  * Created by Hans-Joerg Schurr on 3/10/17.
  */
object BlockedClauseElimination extends CalculusRule {
  override def name = "BCE"
  override def inferenceStatus = SZS_EquiSatisfiable

  /**
    * True if the input clauses set does not contain the inbuilt equality predicate (=).
    * @param clauses Set of clauses.
    * @return True if the input set is equality free.
    */
  def isEqualityFree(clauses: Set[AnnotatedClause])(implicit  sig: Signature) : Boolean = {
    false
  }

  /**
    * This method removes blocked clauses from the matrix. The input problem must be equality free. That means, that
    * the inbuilt equality predicate (=) does not appear.
    *
    * @param clauses the matrix. Must be equality free
    * @return new set of clauses
    */
  def removeBlockedClauses(clauses : Set[AnnotatedClause])(implicit sig: Signature) : Set[AnnotatedClause] = {
    clauses
  }
}
