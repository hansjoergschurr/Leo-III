package leo.modules.boolean_handling

import leo.datastructures.{AnnotatedClause, Literal, Term}
import leo.modules.output.logger.Out
import leo.modules.calculus.mayUnify

import scala.collection.SortedSet

/**
  * Created by hanse on 6/13/16.
  */
object constantExtraction {

  /* TODO:
    - Not unifiable test
    - Search (double iteration!)
    - return list of pure literals (for now)
   */
  def pureLiterals(clauses : SortedSet[AnnotatedClause]) : Set[AnnotatedClause] = {

    /** Tests unifiability approximately. True indicates, that the terms are certainly not unifiable, False
      * indicates that they might be unifiable.
      */
    def notUnifiable(t1: Term, t2: Term): Boolean = {
      !mayUnify(t1, t2)
    }

    val testSet : List[List[(Literal, Boolean)]] = clauses.map((_).cl.map(l => (l, true)).toList).toList

    /*
    def test(l) = {
      case (l::)
    }*/

    Out.debug(s"### Pure literal dedection.")
    for (c <- clauses) {
      Out.debug(s"## Got: ${c.pretty}")
    }
    Set.empty
  }
}
