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
    val testSet : List[List[(Literal, Boolean)]] = clauses.map((_).cl.map(l => (l, !l.equational)).toList).toList

    type LiteralP = (Literal, Boolean)
    type Matrix = List[List[LiteralP]]

    def testClause(c1: List[LiteralP], c2: List[LiteralP]) : (List[LiteralP], List[LiteralP]) = {
      val ch :: cs = c1

      def scanner(t: (LiteralP, List[LiteralP]), lit: LiteralP): (LiteralP, List[LiteralP]) = t match {
        case (_, c2) =>
          var (l1,p1) = lit
          val c2n = for((l2,p2) <- c2) yield {
            // TODO: Extend to equational literals
            if (l1.polarity != l2.polarity &&
              !l1.equational && !l2.equational
              && mayUnify(l1.left, l2.left)) {
              p1 = false
              (l2, false)
            }
            else
              (l2,p2)
          }
          ((l1,p1), c2n)
      }

      val s = cs.scanLeft((ch,c2))(scanner)
      (s.map(_._1), s.last._2)
    }

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

    Out.debug(s"### Pure literal dedection.")

    val pur = test(testSet)

    for (c <- clauses) {
      Out.debug(s"## Got: ${c.pretty}")
    }
    for(c <- pur; (l, p) <- c; if p)
      Out.debug(s"## Pure: ${l.pretty}")

    Set.empty
  }
}
