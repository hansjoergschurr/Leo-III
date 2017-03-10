package leo.modules.special_processing

import leo.datastructures.Term._
import leo.datastructures._
import leo.modules.HOLSignature.o
import leo.modules.calculus
import leo.modules.calculus._
import leo.modules.parsers.Input
import leo.{Checked, LeoTestSuite}

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
    val vargen = freshVarGenFromBlank
    val c = Literal(Input.readFormula(s), true)
    val m = calculus.FullCNF(vargen,Clause.mkUnit(c))
    Set(m map (AnnotatedClause(_,ClauseAnnotation.NoAnnotation)) : _*)
  }

  // p foreach {p => Out.output(p.pretty)}
  test("Universal Reduction: Remove a Universal Variable", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("? [F: ($i > $o)] : (! [X: $o, Y: $i]:( X | (F @ Y)))")
    val p_n = UniversalReduction.removeUniversalVariables(p)
    assert(p_n != p)
    assert(p_n.size == 1)
    assert(p_n.head.cl.lits.size == 1)
  }

  test("Universal Reduction: Remove a Universal Variable 2", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("? [F: ($i > $o)] : (! [X: $o, Y: $i]:((F @ Y) | X))")
    val p_n = UniversalReduction.removeUniversalVariables(p)
    assert(p_n != p)
    assert(p_n.size == 1)
    assert(p_n.head.cl.lits.size == 1)
  }

  test("Universal Reduction: Remove a Universal Variable 3", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("? [F: ($i > $o)] : (! [X: $o, Y: $i]:(((F @ Y) | X) & ( X | (F @ Y))))")
    val p_n = UniversalReduction.removeUniversalVariables(p).toArray
    assert(p_n.length == 2)
    assert(p_n(0).cl.lits.size == 1)
    assert(p_n(1).cl.lits.size == 1)
  }

  test("Universal Reduction: Don't Remove a Universal Variable", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("? [F: ($o > $o)] : (! [X: $o, Y: $i]:( X | (F @ X)))")
    val p_n = UniversalReduction.removeUniversalVariables(p)
    assert(p_n == p)
    assert(p_n.size == 1)
    assert(p_n.head.cl.lits.size == 2)
  }

  test("Universal Reduction: Don't Remove a Universal Variable 2", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("? [F: ($o > $o)] : (! [X: $o, Y: $i]:((F @ X) | X))")
    val p_n = UniversalReduction.removeUniversalVariables(p)
    assert(p_n == p)
  }

  test("Universal Reduction: Don't Remove a Universal Variable 3", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("? [F: ($o > $o)] : (! [X: $o, Y: $i]:(((F @ X) | X) & ( X | (F @ X))))")
    val p_n = UniversalReduction.removeUniversalVariables(p)
    assert(p_n == p)
  }

  test("Universal Reduction: Tautological Clauses", Checked) {
    implicit val s = getFreshSignature

    val p = getCNF("! [X: $o]:((X | ~(X)) & X)")
    val p_n = UniversalReduction.removeUniversalVariables(p)
    assert(p_n.size == 1)
    assert(p_n.head.cl.lits.isEmpty)
  }
}
