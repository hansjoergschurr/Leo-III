package leo.modules.special_processing

import leo.datastructures.{AnnotatedClause, Signature}
import leo.modules.calculus.CalculusRule
import leo.modules.output.{SZS_EquiSatisfiable, SuccessSZS}

/**
  * Created by Hans-Jörg Schurr on 3/10/17.
  */
object BooleanReEncoding extends CalculusRule {
  override def name: String = "BRE"
  override def inferenceStatus: SuccessSZS = SZS_EquiSatisfiable

  /**
    * Replaces literals made up from Boolean universally or existentially quantified variables (Skolem functions) `X`
    * with a new predicate `P(x)`. Furthermore two clauses `P(1)` and `~P(0)` are added to ensure equi-satisfiability.
    * This suppresses primitive substitution.
    *
    * @param clauses The input clauses.
    * @param freshConstants Use two new constants for true (`1`) and false (`0`). This will also change the type of the
    *                       variables.
    * @param replaceInTerms Replaces occurrences of the variables inside of terms too. This is automatically set to
    *                       `true` if `freshConstant` is set to `true`.
    * @param replaceNonSkolem Replaces Boolean functions which are not Skolem functions.
    * @return A new matrix.
    */
  def reencodeBooleans(clauses : Set[AnnotatedClause],
                       freshConstants: Boolean = false,
                       replaceInTerms: Boolean = false,
                       replaceNonSkolem: Boolean = false)(implicit sig: Signature) : Set[AnnotatedClause] = {
    clauses
  }
}
