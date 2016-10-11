package leo.modules.boolean_handling

import leo.datastructures.{AnnotatedClause, Literal, Term}
import leo.modules.output.logger.Out
import leo.modules.sat_solver.PicoSAT

import scala.collection.SortedSet
import scala.collection.immutable.HashMap

/**
  * Created by Hans-Jörg Schurr  on 10/10/16.
  */
object satBasedUnitClause {

  /***
    * Uses a SAT solver to find unit clauses implied by the matrix
    * @param clauses the matrix
    * @return a set of new unit clauses
    */
  def findUnitClauses(clauses : SortedSet[AnnotatedClause]) : Set[AnnotatedClause] = {
    var literalMap : HashMap[Literal, Int] = HashMap();
    val solver = PicoSAT(true);

    var c = clauses.head
    var cs = clauses.tail
    while(cs.nonEmpty) {
      // iterate through matrix and create sat variable
      c = cs.head
      cs = cs.tail
    }
    // solve
    // additions: use decidable unification to add clause
    //    ideas: collect patterns during first iteration
    //            sample clauses containing patterns
    //            use those to create additional clauses
  }
}
