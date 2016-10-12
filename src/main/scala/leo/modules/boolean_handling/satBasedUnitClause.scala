package leo.modules.boolean_handling

import leo.datastructures.{AnnotatedClause, Literal, Term}
import leo.modules.output.logger.Out
import leo.modules.sat_solver.PicoSAT

import scala.collection.SortedSet
import scala.collection.mutable.HashMap

/**
  * Created by Hans-Jörg Schurr  on 10/10/16.
  */
object satBasedUnitClause {

  private def sat_polarity(sat_lit : Int, literal : Literal) =
    literal.polarity match {
      case true => sat_lit
      case false => - sat_lit
    }

  /***
    * Uses a SAT solver to find unit clauses implied by the matrix
    * @param clauses the matrix
    * @return a set of new unit clauses
    */
  def findUnitClauses(clauses : Set[AnnotatedClause]) : Set[AnnotatedClause] = {
    Out.debug(s"### SAT based implied literals.")
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
      solver.addClause(sat_clause)

      c = cs.head
      cs = cs.tail
    }

    Out.debug(s"SAT size:\tVars: ${solver.numVariables} Clauses: ${solver.numAddedClauses}")


    val inverseMap = literalMap.map(_.swap)
    def debugOut(v:Int, pol: Boolean = true) = {
      val Some((l,r)) = inverseMap get v
      val s = pol match {case true => "=="; case false => "!="}
      Out.debug(s"Deduced: ${l.pretty} ${s} ${r.pretty}")
    }

    for (v <- literalMap.valuesIterator) {
      solver.assume(v)
      solver.solve()
      if (solver.state == PicoSAT.UNSAT) debugOut(v:Int)
      solver.assume(-v)
      solver.solve()
      if (solver.state == PicoSAT.UNSAT) debugOut(v:Int, false)

    }
    // wieso == und !=?
    // additions: use decidable unification to add clause
    //    ideas: collect patterns during first iteration
    //            sample clauses containing patterns
    //            use those to create additional clauses
    // Algorithm from An AIG-Based QBF-Solver Using SAT for Preprocessing
    assert(false)
    Set.empty
  }
}
