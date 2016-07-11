package leo.modules.boolean_handling

import leo.datastructures.{AnnotatedClause, Literal, Term}
import leo.modules.output.logger.Out
import leo.modules.calculus.mayUnify

import scala.collection.SortedSet

/**
  * Created by Hans-Jörg Schurr on 6/13/16.
  */
object constantExtraction {

  /* TODO:
    - Not unifiable test
    - Search (double iteration!)
      - is pure: doesn't unify with any literal of opposite polarity
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

    type LiteralP = (Literal, Boolean)
    type Matrix = List[List[LiteralP]]

    def testClause(c1: List[LiteralP], c2: List[LiteralP]) : (List[LiteralP], List[LiteralP]) =
      (c1, c2)

    def search(accu : (List[LiteralP], Matrix), c2: List[LiteralP]) =
      accu match {
        case (c1, accuM) =>
          val (nC1, nC2) = testClause(c1, c2)
          (nC1, nC2::accuM)
      }

    def test(matrix : Matrix) : Matrix =
      matrix match {
        case c :: cs =>
          val(resC, newMatrix) = cs.foldLeft((c, cs))(search)
          resC::test(newMatrix)
        case _  => List()
    }

    test(testSet)
    Out.debug(s"### Pure literal dedection.")
    for (c <- clauses) {
      Out.debug(s"## Got: ${c.pretty}")
    }
    Set.empty
  }
}
