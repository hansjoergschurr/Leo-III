package leo.modules.special_processing

import leo.datastructures.Term._
import leo.datastructures._
import leo.modules.HOLSignature.{===, LitFalse, LitTrue, o}
import leo.modules.calculus.CalculusRule
import leo.modules.output.{SZS_EquiSatisfiable, SuccessSZS}

/**
  * Created by Hans-Jörg Schurr on 3/10/17.
  */
object BooleanReEncoding extends CalculusRule {
  override def name: String = "BRE"
  override def inferenceStatus: SuccessSZS = SZS_EquiSatisfiable

  /**
    * Replaces literals with a new predicate `P(x)`. Furthermore two clauses `P(1)` and `~P(0)` are added to
    * ensure equi-satisfiability. This delays primitive substitution until unification is applied once.
    *
    * @param clauses The input clauses.
    * @param wrapEqualities Wrap equalities
    * @return A new matrix.
    */
  def reencodeBooleans(clauses : Set[AnnotatedClause],
                       wrapEqualities: Boolean = true)(implicit sig: Signature) : Set[AnnotatedClause] = {
    val p = mkAtom(sig.addUninterpreted("BoolEnc", o ->: o))
    val p_true = mkTermApp(p, LitTrue)
    val p_false = mkTermApp(p, LitFalse)
    val c_true = AnnotatedClause(Clause.mkUnit(Literal(p_true, true)), ClauseAnnotation.NoAnnotation)
    val c_false = AnnotatedClause(Clause.mkUnit(Literal(p_false, false)), ClauseAnnotation.NoAnnotation)

    def wrap(lit: Literal) : Literal = {
      if(lit.equational) {
        if(wrapEqualities) {
          Literal(mkTermApp(p, mkTermApp(===, List(lit.left, lit.right))), lit.polarity)
        } else lit
      } else {
        Literal(mkTermApp(p, lit.left), lit.polarity)
      }
    }
    val fresh_c = clauses map { c =>
      val lits = c.cl.lits map wrap
      AnnotatedClause(Clause(lits), c.role, ClauseAnnotation.InferredFrom(BooleanReEncoding, Seq(c, c_true, c_false)) , c.properties)
    }

    fresh_c + c_true + c_false
  }
}
