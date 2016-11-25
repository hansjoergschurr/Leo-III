package leo.modules.boolean_handling

import leo.datastructures.{AnnotatedClause, Literal, Term, Signature}
import leo.modules.output.logger.Out
import leo.modules.sat_solver.PicoSAT

import scala.collection.immutable.HashMap
import scala.collection.immutable.Set
import scala.collection.mutable.{Set => MSet}

/**
  * Created by Hans-Jörg Schurr  on 10/10/16.
  */

class EqualityGraph private (val nodes: Set[Term], val edges: HashMap[Term, Set[Term]])(implicit sig: Signature) {

  def makeChordal() : EqualityGraph = {
    var g = this
    val newEdges = MSet.empty

    var n = this.nodes.head
    var ns = this.nodes.tail
    while(ns.nonEmpty) {
      val neighbors = g.edges.getOrElse(n, Set.empty)
      //for (l <- neighbors;
      //     j <- neighbors; (l != j) && l.compareTo(j) ==   )

      n = ns.head
      ns = ns.tail
    }
    this
  }

  def addEdge(l: Term, j: Term) : EqualityGraph = {
    val a_adj = this.edges.getOrElse(l, Set.empty) + j
    val b_adj = this.edges.getOrElse(j, Set.empty) + l
    val edges = this.edges.updated(l, a_adj).updated(j, b_adj)
    EqualityGraph(this.nodes, edges)
  }

  def deleteNode(l: Term) : EqualityGraph = {
    val neighbors = this.edges.getOrElse(l, Set.empty)
    val ne = neighbors.foldLeft(this.edges) ((es,j) => es.updated(j, es.getOrElse(j, Set.empty) - j))
    EqualityGraph(this.nodes - l, ne)
  }

  def iterateConstraints() : List[(Term, Term, Term)] = {
    List.empty
  }
}

object EqualityGraph {
  def apply(nodes: Set[Term], edges: HashMap[Term, Set[Term]])(implicit sig: Signature): EqualityGraph = {
    EqualityGraph(nodes, edges)
  }
}

object SatBasedUnitClauses {

  private def sat_polarity(sat_lit : Int, literal : Literal) =
    literal.polarity match {
      case true => sat_lit
      case false => - sat_lit
    }

  /***
    * Uses a SAT solver to find unit clauses implied by the matrix.
    * @param clauses the matrix
    * @return a set of new unit clauses
    */
  def findUnitClauses(clauses : Set[AnnotatedClause])(implicit sig: Signature) : Set[AnnotatedClause] = {
    Out.debug(s"### SAT based unit clauses.")
    var literalMap : HashMap[(Term,Term), Int] = HashMap();
    val solver = PicoSAT(true);

    // Generate SAT problem
    var c = clauses.head
    var cs = clauses.tail
    while(cs.nonEmpty) {
      var sat_clause = List.empty[Int]

      for (l <-  c.cl.lits) {
        val sat_val = literalMap get (l.left, l.right)
        sat_val match {
          case Some(sat_lit) => sat_clause = sat_polarity(sat_lit, l) :: sat_clause
          case None => val fresh = solver.freshVariable
                          literalMap += ((l.left, l.right) -> fresh)
                          sat_clause = sat_polarity(fresh, l) :: sat_clause
        }
      }
      Out.trace{s"Added to SAT problem: ${sat_clause}."}
      solver.addClause(sat_clause)

      c = cs.head
      cs = cs.tail
    }

    Out.debug(s"SAT problem size:\tVars: ${solver.numVariables} Clauses: ${solver.numAddedClauses}")

    // Output helpers
    val inverseMap = literalMap.map(_.swap)
    def debugOut(v:Int) = {
      val Some((l,r)) = inverseMap get v.abs
      val s = v > 0 match {case true => "=="; case false => "!="}
      Out.debug(s"Deduced: ${l.pretty} ${s} ${r.pretty}")
    }

    val satLiteralSet = MSet[Int]()
    if(solver.solve() == PicoSAT.SAT){
      for(v <- literalMap.values) {
        solver.getAssignment(v) match {
          case Some(true) => satLiteralSet.add(-v)
            solver.setDefaultPhase(v, -1) // facilitates the removal of variables to check
          case Some(false) => satLiteralSet.add(v)
            solver.setDefaultPhase(v, 1)
          case None => ;
        }
      }
    }
    else if(solver.solve() == PicoSAT.UNSAT) {
      Out.debug(s"Base SAT problem UNSAT. Input clauses contradictory.")
      assert(false)
    }
    else {
      Out.debug(s"Base SAT problem undecided.")
      assert(false)
    }

    Out.trace(s"Vars to test after first model: ${satLiteralSet.size}")

    while (satLiteralSet.nonEmpty) {
      val v = satLiteralSet.head
      satLiteralSet.remove(v)
      Out.trace{s"Testing ${v}."}

      solver.assume(v)
      if (solver.solve() == PicoSAT.UNSAT) debugOut(-v:Int)
      else if (solver.solve() == PicoSAT.SAT) {
        satLiteralSet.retain(solver.getAssignment(_).contains(false))
      }
      Out.trace(s"Vars to test: ${satLiteralSet.size}")
    }
    // additions: use decidable unification to add clause
    //            add equality consts: a=b /\ b = c => a =c
    //    ideas: collect patterns during first iteration
    //            sample clauses containing patterns
    //            use those to create additional clauses
    // Algorithm from An AIG-Based QBF-Solver Using SAT for Preprocessing
    // TODO: Add the found clouses and activate the controll
    //assert(false)
    scala.collection.immutable.Set.empty
  }
}
