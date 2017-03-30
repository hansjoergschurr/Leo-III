package leo.modules.special_processing

import leo.datastructures.Term.Bound
import leo.datastructures._
import leo.modules.HOLSignature.===
import leo.modules.calculus.{CalculusRule, PatternUnification}
import leo.modules.output.SZS_EquiSatisfiable
import leo.modules.output.logger.Out

import scala.collection.mutable
import scala.collection.mutable.{HashMap, MultiMap, Set}

/** Index data structure for patterns. Maps literals + polarity to clauses and literals with
  * same head predicate or free head.
  */
class PatternIndex(implicit sig: Signature) {
  private val rigidIndex =
    new HashMap[(Boolean, Term), Set[(Clause, Literal)]] with MultiMap[(Boolean, Term), (Clause, Literal)]
  private val flex = Set[(Clause, Literal)]()
  private val rigid = Set[(Clause, Literal)]()

  def addClauseLiteralPair(cl: Clause, l: Literal) : Unit = {
    assert(PatternUnification.isPattern(l.left))
    val head = l.left.headSymbol
    val pol = l.polarity
    if (head.isVariable) {
      // Flex case
      flex.add((cl, l))
    }
    else {
      // Rigid case
      rigid.add((cl, l))
      rigidIndex.addBinding((pol, head), (cl, l))
    }
  }

  def lookupResCandidates(l: Literal) : Set[(Clause, Literal)] = {
    val head = l.left.headSymbol
    val pol = l.polarity
    if (head.isVariable) {
      rigid union flex
    }
    else {
      val r = rigidIndex.getOrElse((!pol, head), Set.empty)
      r union flex
    }
  }

  def lookupResCandidatesInClause(l: Literal, c: Clause) : Set[Literal] =
  { lookupResCandidates(l).flatMap(t => if (t._1 == c) Some(t._2) else None)}

  def resCandidatesByClause(l: Literal): Seq[(Clause, Set[Literal])] =
  {
    val s = lookupResCandidates(l)
    val out = new HashMap[Clause, Set[Literal]] with MultiMap[Clause, Literal]
    s.foreach(cl => out.addBinding(cl._1, cl._2))
    out.toSeq
  }

  def numTotalPartners(l: Literal) : Int = {lookupResCandidates(l).size}

  def removeClause(c: Clause) : Unit = {
    flex.retain(_._1 != c)
    rigid.retain(_._1 != c)
    rigidIndex.mapValues(s => {s.retain(_._1 != c); s})
  }

  def debugOutput() : Unit = {
    Out.debug(s"Pattern stats:")
    Out.debug(s"\tFlex: ${flex.size}")
    Out.debug(s"\tRigid: ${rigid.size}")
    Out.debug(s"\tRigid Index Keys: ${rigidIndex.keys.size}")
  }
}

class Deactivations(implicit sig: Signature) {
  private val deactivatedBy = new HashMap[(Clause, Literal), Set[Clause]] with MultiMap[(Clause, Literal), Clause]
  private val deactivates =  new HashMap[Clause, Set[(Clause, Literal)]] with MultiMap[Clause, (Clause, Literal)]

  def deactivates(deactivator: Clause, deactivated: (Clause, Literal)) {
    deactivatedBy.addBinding(deactivated, deactivator)
    deactivates.addBinding(deactivator, deactivated)
  }

  def isDeactivated(deactivated: (Clause, Literal)): Boolean = deactivatedBy(deactivated).nonEmpty

  def removeDeactivator(deactivator: Clause): Set[(Clause, Literal)] = {
    val d = deactivates(deactivator)
    deactivates.remove(deactivator)
    d.foreach(cl => deactivatedBy.removeBinding(cl, deactivator))
    d.filter(cl => deactivatedBy(cl).isEmpty)
  }

  def numDeactivated : Int = deactivatedBy.keys.size
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
  def isEqualityFree(clauses: scala.collection.immutable.Set[AnnotatedClause])(implicit  sig: Signature) : Boolean = {
    clauses.forall(_.cl.lits.forall( l => {
      ! (l.equational ||
        l.left.symbols.contains(===.key) ||
        l.right.symbols.contains(===.key))
    }))
  }

  /**
    *
    * @param C clause one
    * @param blockingLit potential blocking lit
    * @param D partner clause
    * @param partners literals potentially unifiable with `blockingLit` e.g. have the same head symbol of flex-head and are all patterns
    * @param sig
    * @return true if `blockingLit` is blocking C rel. to D
    */
  def isNotResOrValid(C: Clause, blockingLit: Literal, D: Clause, partners: Set[Literal])(implicit sig: Signature) : Boolean = {
    val resolvent = Clause(C.lits ++ D.lits)
    val vargen = leo.modules.calculus.freshVarGen(resolvent)
    val maxFree = C.maxImplicitlyBound
    val D_lifted = D.substitute(Subst.shift(maxFree))

    val blocking_const = blockingLit.left
    val partners_const = partners.map(_.left.lift(maxFree))

    partners_const.forall(s => {
      var n=Set(s)

      val v = PatternUnification.unifyAll(vargen.copy, ???)
      val subst = v.head._1
      val c = resolvent.substitute(subst._1, subst._2)
      val c2 = leo.modules.calculus.Simp(c)
      Clause.trivial(c2)
      // find all complementary literals ()

      false
    })

    //val resLit_lifted = resLit.substitute(Subst.shift(maxFree))
    //val uni = PatternUnification.unify(vargen, blockingLit.left, resLit_lifted.left)
    true
  }

  /**
    * This method removes blocked clauses from the matrix. The input problem must be equality free. That means, that
    * the inbuilt equality predicate (=) does not appear.
    *
    * @param clauses the matrix. Must be equality free
    * @return new set of clauses
    */
  def removeBlockedClauses(clauses : scala.collection.immutable.Set[AnnotatedClause])(implicit sig: Signature) : scala.collection.immutable.Set[AnnotatedClause] = {
    assert(isEqualityFree(clauses))

    // Iterate once and separate
    //  -> Pattern Literal: Create (C, L) pair and add to Index
    //  -> Non-pattern with flex head: Killer can't have more then two!
    //  -> Non-pattern with bound head: Create mapping (Head, Polarity) -> (C, L)
    //    -> Deactivate (C, L) pattern pairs that have a head in the non-pattern mapping with foreign clause

    val rigidPatternIndex = new PatternIndex
    val rigidNonPatterns = new HashMap[(Boolean, Term), Set[(Clause, Literal)]] with MultiMap[(Boolean, Term), (Clause, Literal)]

    var clauseLiteralPairs = List[(Clause, Literal)]()
    var clauseContainingFlexNP : Option[Clause] = None
    // Find all clause literal pairs and add literals to indices
    clauses.foreach(ac => {
      val c = ac.cl
      c.lits.foreach(l => {
        if(PatternUnification.isPattern(l.left)) {
          rigidPatternIndex.addClauseLiteralPair(c,l)
          clauseLiteralPairs = (c, l)::clauseLiteralPairs
        }
        else { // non-pattern case
          l.left.headSymbol match {
          // Flex case (evil one)
          case Bound(_, _) =>
            clauseContainingFlexNP match {
              case None => clauseContainingFlexNP = Some(c)
              case Some(c2) => if (c != c2) {
                Out.debug{"Found two different clauses with non-pattern literals with flex head. Aborting Blocked Clause Elimination."}
                return clauses
              }
            }
          // Rigid case
          case head =>
            rigidNonPatterns.addBinding((l.polarity, head), (c, l))
          }
        }
      })
    })

    // Add clause literal pairs to queue and deactivate appropriately
    val deactivations = new Deactivations()
    val queue = new mutable.PriorityQueue[((Clause, Literal), Int)]()(Ordering.by(_._2))

    clauseContainingFlexNP match {
      case Some(c:Clause) => {
        // Deactivate all pairs except the ones induced by c
        Out.debug(s"Found one clause containing non-pattern with flex head. Deactivating all other clauses.")
        c.lits.foreach{l =>
          if (PatternUnification.isPattern(l.left)) {
            queue.enqueue((c,l) -> rigidPatternIndex.numTotalPartners(l))
          }
        }
        clauseLiteralPairs.foreach(cl => {
          deactivations.deactivates(c, cl)
        })
      }
      case None => {
        // Either add to queue, or deactivate if rigid non patterns with same head and opposite polarity are found.
        Out.debug(s"Found no clause containing non-pattern with flex head.")
        clauseLiteralPairs.foreach((cl: (Clause, Literal)) => {
          val rnp = if(cl._2.flexHead) {
            // If flex I could potentially unify with rigid heads of both polarities.
            rigidNonPatterns((cl._2.polarity, cl._2.left)) union rigidNonPatterns((! cl._2.polarity, cl._2.left))
            }
          else rigidNonPatterns((! cl._2.polarity, cl._2.left))
          if(rnp.isEmpty) {
            queue.enqueue(cl -> rigidPatternIndex.numTotalPartners(cl._2))
          }
          else {
            rnp.foreach(d_cl => deactivations.deactivates(d_cl._1, cl))
          }
        })
      }
    }

    rigidPatternIndex.debugOutput()
    Out.debug(s"Deactivated pairs: ${deactivations.numDeactivated}.")

    val foundBlocked = Set.empty[Clause]

    while (queue.nonEmpty) {
      val ((c,l), _) = queue.dequeue()
      val s = rigidPatternIndex.resCandidatesByClause(l)
      val blocked = s.forall(cl => {
        val c2 = cl._1 //Partner Clause
        val ls = cl._2 //Partner Literal
        val b = testValidityRes(c, l, c2, ls) : Boolean
        if(!b) {
          deactivations.deactivates(c2, (c,l))
          false
        }
        else true
      })
      if (blocked) {
        foundBlocked.add(c)
        rigidPatternIndex.removeClause(c)
        val reactivated = deactivations.removeDeactivator(c)
        reactivated.foreach(cl => queue.enqueue((cl._1, cl._2) -> rigidPatternIndex.numTotalPartners(cl._2)))
      }
    }

    Out.debug(s"Found blocked: ${foundBlocked.size}")
    clauses.filter(ac => !foundBlocked.contains(ac.cl))
  }
}
