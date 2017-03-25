package leo.modules.special_processing

import leo.datastructures.Term.Bound
import leo.datastructures._
import leo.modules.HOLSignature.===
import leo.modules.calculus.{CalculusRule, PatternUnification, mayUnify}
import leo.modules.output.SZS_EquiSatisfiable

import scala.collection.mutable
import scala.collection.mutable.{HashMap, MultiMap, Set}

/** Index data structure for patterns. Maps literals + polarity to clauses and literals with
  * same head predicate or free head.
  */
class PatternIndex(implicit sig: Signature) {
  private val rigidIndex =
    new HashMap[(Boolean, Term), Set[(Clause, Literal)]] with MultiMap[(Boolean, Term), (Clause, Literal)]
  private val flexPositive = Set[(Clause, Literal)]()
  private val flexNegative = Set[(Clause, Literal)]()
  private val rigidPositive = Set[(Clause, Literal)]()
  private val rigidNegative = Set[(Clause, Literal)]()

  def addClauseLiteralPair(cl: Clause, l: Literal) : Unit = {
    assert(PatternUnification.isPattern(l.left))
    val head = l.left.headSymbol
    val pol = l.polarity
    val f = if (pol) flexPositive else flexNegative
    val r = if (pol) rigidPositive else rigidNegative
    head match {
        // Flex case
      case Bound(_, _) =>
       f.add((cl, l))
        // Rigid case
      case _ =>
        r.add((cl, l))
        rigidIndex.addBinding((pol, head), (cl, l))

    }
  }

  def lookupResCandidates(l: Literal) : Set[(Clause, Literal)] = {
    val head = l.left.headSymbol
    val pol = l.polarity
    head match {
      // Flex case
      case Bound(_, _) =>
        if (pol) { flexNegative union rigidNegative }
        else { flexPositive union rigidPositive } //select the inverse polarity
      // Rigid case
      case _ =>
        val r = rigidIndex.getOrElse((!pol, head), Set.empty)
        val f = if (pol) flexNegative else flexPositive //select the inverse polarity
        r union f
    }
  }

  def lookupResCandidatesInClause(l: Literal, c: Clause) : Set[Literal] =
  { lookupResCandidates(l).flatMap(t => if (t._1 == c) Some(t._2) else None)}

  def numTotalPartners(l: Literal) : Int = {lookupResCandidates(l).size}
}

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

  def isNotResOrValid(C: Clause, D: Clause, blockingLit: Term, resLit: Term)(implicit sig: Signature) : Boolean = {
    if(mayUnify(blockingLit, resLit)) {
      if (!PatternUnification.isPattern(resLit)) false
      else {
        val maxFree = C.maxImplicitlyBound
        val D_lifted = D.substitute(Subst.shift(maxFree))
        val resLit_lifted = resLit.substitute(Subst.shift(maxFree))
        val resolvent = Clause(C.lits ++ D.lits)
        val vargen = leo.modules.calculus.freshVarGen(resolvent)
        val uni = PatternUnification.unify(vargen, blockingLit, resLit_lifted)
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

    // Iterate once and separate
    //  -> Pattern Literal: Create (C, L) pair and add to Index
    //  -> Non-pattern with flex head: Killer can't have more then two!
    //  -> Non-pattern with bound head: Create mapping (Head, Polarity) -> (C, L)
    //    -> Deactivate (C, L) pattern pairs that have a head in the non-pattern mapping with foreign clause


    val rigidPatternIndex = new PatternIndex
    val rigidNonPatterns = new HashMap[(Boolean, Term), Set[(Clause, Literal)]] with MultiMap[(Boolean, Term), (Clause, Literal)]
    var deactivatedPairs = List[(Clause, Literal)]()

    clauses.foreach(ac => {
      val c = ac.cl
      c.lits.foreach(l => {
        if(PatternUnification.isPattern(l.left)) {
          rigidPatternIndex.addClauseLiteralPair(c,l)
          deactivatedPairs = (c, l)::deactivatedPairs
        }
        else {
          l.left.headSymbol match {
          // Flex case
          case Bound(_, _) =>
            // here be dragons!
            ()
          // Rigid case
          case head =>
            rigidNonPatterns.addBinding((l.polarity, head), (c, l))
          }
        }
      })
    })

    val queue = mutable.PriorityQueue
    var foundBlocked = Set.empty[AnnotatedClause]

    //TODO: optimize a bit
    for (possibleBlocked <- clauses) {
      for (possibleBlockingLit <- possibleBlocked.cl.lits.map(_.left).withFilter(PatternUnification.isPattern)) {
        val isBlocked = clauses.forall(c => c == possibleBlocked || c.cl.lits.forall(l =>
          isNotResOrValid(possibleBlocked.cl, c.cl, possibleBlockingLit, l.left)))
        if(isBlocked) foundBlocked = foundBlocked + possibleBlocked
      }
    }
    clauses
  }
}
