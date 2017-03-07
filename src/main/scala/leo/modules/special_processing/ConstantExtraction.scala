package leo.modules.special_processing

import leo.datastructures.{AnnotatedClause, Literal, Term}
import leo.modules.output.logger.Out
import leo.modules.calculus.mayUnify

import scala.collection.SortedSet

/**
  * Created by Hans-Jörg Schurr on 6/13/16.
  */
object ConstantExtraction {

  /*  This file attempts to find literals not unifiable with any other literal. It was the first
      algorithm implemented, but is certainly unsound.

      Do not use this code.
   */
  def pureLiterals(clauses : SortedSet[AnnotatedClause]) : Set[AnnotatedClause] = {
    type LiteralP = (Literal, Boolean)

    def testClause(c1p: AnyRef, c2p: AnyRef) : (Seq[LiteralP], Seq[LiteralP]) = {
      val c1 = c1p.asInstanceOf[Seq[LiteralP]]
      var c2 = c2p.asInstanceOf[Seq[LiteralP]]

      def loop(x: LiteralP): LiteralP = {
        var (l1, p1) = x
        c2 = c2.map {
          case (l2, p2) =>
            // TODO: Extend to equational literals
            if ((l1.polarity != l2.polarity) &&
              !l1.equational && !l2.equational
              && mayUnify(l1.left, l2.left)) {
              p1 = false
              Out.debug(s"Found counter ex.: ${l1.pretty}, ${l2.pretty}")
              (l2, false)
            }
            else
              (l2, p2)
        }
        (l1, p1)
      }

      val c1n = c1.map(loop)

      (c1n, c2)
    }

    Out.debug(s"### Pure literal detection.")

    clauses.foreach(c => c.additionalInformation = Some(c.cl.map(l => (l, !l.equational))))
    var c = clauses.head
    var cs = clauses.tail

    while(cs.nonEmpty) {
      Out.debug(s"Iterations left: ${cs.size}")
      cs.foreach(c2 => {
        val (c1p, c2p) = testClause(c.additionalInformation.get,c2.additionalInformation.get)
        c2.additionalInformation = Some(c2p)
        c.additionalInformation = Some(c1p)
      })

      c = cs.head
      cs = cs.tail
    }

    val pur = clauses.flatMap(c => c.additionalInformation.get.asInstanceOf[Seq[LiteralP]].filter(_._2))

    for (c <- clauses) {
      Out.debug(s"## Got: ${c.pretty}")
    }
    for(c <- pur) {
      val (l, p) = c
      if(p)
        Out.debug(s"## Pure: ${l.pretty}")
    }
    assert(false)
    Set.empty
  }
}
