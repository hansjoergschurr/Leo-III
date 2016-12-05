package leo.modules.boolean_handling

import leo.datastructures.{AnnotatedClause, Literal, Term, Signature}
import leo.modules.output.logger.Out
import leo.modules.sat_solver.PicoSAT

import scala.collection.immutable.HashMap
import scala.collection.immutable.Set
import scala.collection.mutable.{Set => MSet, HashMap => MHashMap}

/**
  * Created by Hans-Jörg Schurr  on 10/10/16.
  */

class EqualityGraph private (val nodes: Set[Term], val edges: HashMap[Term, Set[Term]])(implicit sig: Signature) {

  def chordal : EqualityGraph = {
    if (this.nodes.isEmpty) {return this}
    var g = this
    var newEdges = List[(Term,Term)]()

    val sortedNodes = this.nodes.toList.sortWith((a, b) => this.neighbors(a).size < this.neighbors(b).size)
    var ns = sortedNodes
    while(ns.nonEmpty) {
      val n = ns.head
      val neighbors = g.edges.getOrElse(n, Set.empty)
      for {
        l <- neighbors
        j <- neighbors
        if (l != j) && Term.LexicographicalOrdering.gt(l,j)} {
        g = g.addEdge(l,j)
        newEdges = (l,j)::newEdges
      }
      g = g.deleteNode(n)

      ns = ns.tail
    }

    newEdges.foldLeft(this) { case (g:EqualityGraph,(l:Term, j:Term)) => g.addEdge(l,j) }
  }

  def neighbors(n: Term): Set[Term] = {
    this.edges.getOrElse(n, Set.empty)
  }

  def addEdge(l: Term, j: Term) : EqualityGraph = {
    val a_adj = this.edges.getOrElse(l, Set.empty) + j
    val b_adj = this.edges.getOrElse(j, Set.empty) + l
    val edges = this.edges.updated(l, a_adj).updated(j, b_adj)
    EqualityGraph(this.nodes + l + j, edges)
  }

  def deleteNode(l: Term) : EqualityGraph = {
    val neighbors = this.edges.getOrElse(l, Set.empty)
    val ne = neighbors.foldLeft(this.edges) ((es,j) => es.updated(j, es.getOrElse(j, Set.empty) - l))
    EqualityGraph(this.nodes - l, ne)
  }

  def constraints : Set[(Term, Term, Term)] = {
      for {
        n <- this.nodes
        l <- this.neighbors(n); j <- this.neighbors(n)
        if l != j
        if Term.LexicographicalOrdering.gt(l,j)
        if this.neighbors(l).contains(j)
      } yield (n,l,j)
  }
}

object EqualityGraph {
  def apply(nodes: Set[Term] = Set.empty, edges: HashMap[Term, Set[Term]] = HashMap.empty)(implicit sig: Signature): EqualityGraph = {
    new EqualityGraph(nodes, edges)
  }
}

object SatBasedUnitClauses {

  private def sat_polarity(sat_lit : Int, literal : Literal) =
    literal.polarity match {
      case true => sat_lit
      case false => - sat_lit
    }

  private def order_terms(a: Term, b : Term) : (Term, Term) =
  {if (Term.LexicographicalOrdering.gt(a,b)) (a,b) else (b,a)}

  private def getSATLiteral(l: (Term, Term), s : PicoSAT)(implicit m: MHashMap[(Term,Term), Int]) : Int = {
    m get l match {
      case Some(sat_lit) => sat_lit
      case None =>
        val fresh = s.freshVariable
        m put (l, fresh)
        fresh
      }
  }


  /***
    * Uses a SAT solver to find unit clauses implied by the matrix.
    * @param clauses the matrix
    * @return a set of new unit clauses
    */
  def findUnitClauses(clauses : Set[AnnotatedClause])(implicit sig: Signature) : Set[AnnotatedClause] = {
    Out.debug(s"### SAT based unit clauses.")
    implicit val literalMap : MHashMap[(Term,Term), Int] = MHashMap()
    val solver = PicoSAT(true)

    val oldUnitClauses : MSet[(Term,Term)]  = MSet()

    // Generate SAT problem and Equality Graph
    var eq_g = EqualityGraph()
    var c = clauses.head
    var cs = clauses
    while(cs.nonEmpty) {
      val c = cs.head
      var sat_clause = List.empty[Int]

      if(c.cl.lits.size == 1) {
        val l = c.cl.lits.head
        oldUnitClauses.add(order_terms(l.left, l.right))
      }

      for (l <-  c.cl.lits) {
        val literal = order_terms(l.left, l.right)
        val sat_val = getSATLiteral(literal, solver)
        sat_clause = sat_polarity(sat_val, l) :: sat_clause
        if (l.equational) eq_g = eq_g.addEdge(l.left,l.right)
      }
      Out.trace(s"Added to SAT problem: $sat_clause.")
      solver.addClause(sat_clause)

      cs = cs.tail
    }

    Out.debug(s"SAT problem size before EQ:\tVars: ${solver.numVariables} Clauses: ${solver.numAddedClauses}")

    // Add Equality Constraints
    Out.debug(s"Equality Graph size:\tNodes: ${eq_g.nodes.size} Edges: ${eq_g.edges.values.map(_.size).sum/2}")
    eq_g = eq_g.chordal
    Out.debug(s"Chordal Equality Graph size:\tNodes: ${eq_g.nodes.size} Edges: ${eq_g.edges.values.map(_.size).sum/2}")
    for((a,b,c) <- eq_g.constraints) { // generate a=b ∧ b=c => a=c
      val (c1,c2,c3) = (order_terms(a,b), order_terms(b,c), order_terms(a,c))
      val (l1,l2,l3) = (getSATLiteral(c1, solver), getSATLiteral(c2,solver), getSATLiteral(c3, solver))
      solver.addClause(-l1,-l2,l3)
    }
    Out.debug(s"SAT problem size after EQ:\tVars: ${solver.numVariables} Clauses: ${solver.numAddedClauses}")

    // Output helpers
    val inverseMap = literalMap.map(_.swap)
    def debugOut(v:Int) = {
      val Some((l,r)) = inverseMap get v.abs
      val s = v > 0 match {case true => "=="; case false => "!="}
      if (oldUnitClauses.contains((l,r))) {
        Out.debug(s"Didn't deduce already known: ${l.pretty} $s ${r.pretty}")
      }
      else
        Out.debug(s"Deduced: ${l.pretty} $s ${r.pretty}")
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
      assert(false) // TODO: sensible result
    }
    else {
      Out.debug(s"Base SAT problem undecided.")
      assert(false) // TODO: sensible result
    }

    Out.trace(s"Vars to test after first model: ${satLiteralSet.size}")

    while (satLiteralSet.nonEmpty) {
      val v = satLiteralSet.head
      satLiteralSet.remove(v)
      Out.trace{s"Testing $v."}

      solver.assume(v)
      if (solver.solve() == PicoSAT.UNSAT) debugOut(-v:Int)
      else if (solver.solve() == PicoSAT.SAT) {
        satLiteralSet.retain(solver.getAssignment(_).contains(false))
      }
      Out.trace(s"Vars to test: ${satLiteralSet.size}")
    }
    // Algorithm from: An AIG-Based QBF-Solver Using SAT for Preprocessing
    // EQ graph from: Boolean Satisfiability with Transitivity Constraints
    // TODO: Add the found clauses and activate the control
    assert(false)
    scala.collection.immutable.Set.empty
  }
}
