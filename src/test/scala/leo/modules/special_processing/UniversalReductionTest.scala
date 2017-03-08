package leo.modules.special_processing

import leo.datastructures._
import Term._
import leo.{Checked, LeoTestSuite}
import leo.modules.HOLSignature.o
import leo.modules.calculus._
import leo.modules.control.Control
import leo.modules.output.logger.Out
import leo.modules.parsers.Input

/**
  * Created by Hans-Jörg Schurr on 3/8/17.
  */
class UniversalReductionTest extends LeoTestSuite {

  test("Universal Reduction: Lit Is Boolean Var", Checked){
    implicit val s = getFreshSignature
    val vargen = freshVarGenFromBlank

    val t = vargen(o)
    val l1 = Literal(t, true)
    val l2 = Literal(t, false)
    assert(!l1.equational)
    assert(l1.left.isVariable)
    assert(l1.left.ty == o)
    assert(UniversalReduction.litIsBooleanVar(l1))
    assert(UniversalReduction.litIsBooleanVar(l2))
  }

  test("Universal Reduction: Equational Lit Is Not Boolean Var", Checked){
    implicit val s = getFreshSignature
    val vargen = freshVarGenFromBlank

    val t1 = vargen(o)
    val t2 = vargen(o)
    val l1 = Literal(t1, t2, true)
    val l2 = Literal(t1, t2, false)
    assert(!UniversalReduction.litIsBooleanVar(l1))
    assert(!UniversalReduction.litIsBooleanVar(l2))
  }

  test("Universal Reduction: Complex Term is Not Boolean Var", Checked){
    implicit val s = getFreshSignature
    val vargen = freshVarGenFromBlank

    val f = mkAtom(s.addUninterpreted("f", o ->: o))
    val t = mkTermApp(f, vargen(o))
    val l1 = Literal(t, true)
    val l2 = Literal(t, false)
    assert(!UniversalReduction.litIsBooleanVar(l1))
    assert(!UniversalReduction.litIsBooleanVar(l2))
  }

  private def getCNF(s: String)(implicit sig: Signature) : Set[AnnotatedClause] = {
    val c = Seq(Literal(Input.readFormula(s), true))
    val p = AnnotatedClause(Clause.mkClause(c), ClauseAnnotation.NoAnnotation)
    Control.cnf(p)
  }

  //Tests: Remove from clause, don't remove, tautological, multiple clauses
  test("Universal Reduction: Remove a Universal Variable", Checked) {
    implicit val s = getFreshSignature

    val problem = getCNF("?[X1:$o]:X1")
    problem foreach {p => Out.output(o.pretty)}
  }
}
