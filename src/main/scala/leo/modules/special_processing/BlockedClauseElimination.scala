package leo.modules.special_processing

import leo.datastructures._
import leo.modules.HOLSignature.===
import leo.modules.calculus.{CalculusRule, PatternUnification, mayUnify}
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
    clauses.forall(_.cl.lits.forall( l => {
      ! (l.equational ||
        l.left.symbols.contains(===.key) ||
        l.right.symbols.contains(===.key))
    }))
  }

  def isNotResOrValid(C: Clause, D: Clause, blockingLit: Term, resLit: Term): Boolean = {
    if(mayUnify(blockingLit, resLit)) {
      if (!PatternUnification.isPattern(resLit)) false
      else {
        false
      }
    }
    else true
  }

  /**
    * This method removes blocked clauses from the matrix. The input problem must be equality free. That means, that
    * the inbuilt equality predicate (=) does not appear.
    *
    * @param clauses the matrix. Must be equality free
    * @return new set of clauses
    */
  def removeBlockedClauses(clauses : Set[AnnotatedClause])(implicit sig: Signature) : Set[AnnotatedClause] = {
    assert(isEqualityFree(clauses))

    var foundBlocked = Set.empty[AnnotatedClause]

    //TODO: optimize a bit
    for (possibleBlocked <- clauses) {
      for (possibleBlockingLit <- possibleBlocked.cl.lits.map(_.left).withFilter(PatternUnification.isPattern)) {
        val isBlocked = clauses.forall(c => c == possibleBlocked || c.cl.lits.forall(l =>
          isNotResOrValid(possibleBlocked.cl, c.cl, possibleBlockingLit, l.left)))
        if(isBlocked) foundBlocked = foundBlocked + possibleBlocked
      }
    }
  }
}
