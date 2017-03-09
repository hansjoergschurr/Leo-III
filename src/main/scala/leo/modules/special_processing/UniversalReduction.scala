package leo.modules.special_processing

import leo.datastructures._
import leo.modules.HOLSignature.o
import leo.modules.calculus.CalculusRule
import leo.modules.output.SZS_EquiSatisfiable
import leo.modules.output.logger.Out

/**
  * Created by Hans-Jörg Schurr on 3/7/17.
  */
object UniversalReduction extends CalculusRule {

  val name = "UnivRed"
  val inferenceStatus = SZS_EquiSatisfiable

  def litIsBooleanVar(l: Literal) : Boolean = {
    !l.equational && l.left.isVariable && l.left.ty == o
  }

  private def allBooleanVars(t: Term) : Set[Term] = {
    t.freeVars.filter(_.ty == o)
  }

  /**
    * This method removes universally quantified variables from clauses. Such variables can be removed, if
    * they appear only as individual literals, and nowhere else.
    * Furthermore, clauses which contain universally quantified boolan variables as literal in both polarities
    * are removed because they are tautological.
    *
    * @param clauses the matrix
    * @return new set of clauses
    */
  def removeUniversalVariables(clauses : Set[AnnotatedClause])(implicit sig: Signature) : Set[AnnotatedClause] = {
    clauses.flatMap { c =>
      val booleanVarLiterals = Set((for (l <- c.cl.lits if litIsBooleanVar(l)) yield (l.left, l.polarity)) : _*)
      Out.trace(s"Found literals of Boolean variable literals: ${booleanVarLiterals.size}")

      // test if clause is tautological
      if(!booleanVarLiterals.forall(l => !booleanVarLiterals.contains(l._1, !l._2))) {
        Out.trace(s"Clause ${c.pretty} is tautological.")
        None
      }
      else {
        var blnVars = booleanVarLiterals.map(_._1)
        for (l <- c.cl.lits) {
          if (l.equational) {
            val remove = allBooleanVars(l.left) union allBooleanVars(l.right)
            blnVars = blnVars -- remove
          }
          else if (!litIsBooleanVar(l)) {
            blnVars = blnVars -- allBooleanVars(l.left)
          }
        }
        val newClause = Clause(c.cl.lits.filter(l => {
          l.equational || !l.left.isVariable || !blnVars.contains(l.left)
        }))
        if(newClause != c.cl) {
          Out.trace(s"Universal reduction: ${c.cl.pretty} -> ${newClause.pretty}")
          Some(AnnotatedClause(newClause, c.role, ClauseAnnotation.InferredFrom(UniversalReduction, c), c.properties))
        } else Some(c)
      }
    }
  }
}
