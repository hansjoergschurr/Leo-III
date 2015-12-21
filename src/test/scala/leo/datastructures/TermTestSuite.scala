package leo.datastructures

import scala.language.implicitConversions

import leo.LeoTestSuite

/**
 * Created by lex on 23.04.15.
 */
class TermTestSuite extends LeoTestSuite {


  // Meta variable instantiation test
  import Term.{λ, intToBoundVar, mkMetaVar}
  import impl.Signature

  val sig = Signature.get
  val o = sig.o
  val i = sig.i
  val metaVarInstTestTerms = Map(
    1 -> λ(o)(|||((1,o), mkMetaVar(o, 1))).betaNormalize,
    2 -> &(Forall(λ(o)(|||((1,o),Not(mkMetaVar(o,1))))), mkMetaVar(o,2)).betaNormalize
  )

  val metaVarInstTestSubst = Map(
    1 -> Subst.id,
    2 -> (TermFront(LitTrue) +: Subst.id),
    3 -> (TermFront(LitFalse) +: TermFront(LitTrue) +: Subst.id),
    4 -> (BoundFront(1) +: TermFront(LitTrue) +: Subst.id),
    5 -> (BoundFront(2) +: TermFront(LitTrue) +: Subst.id)
  )

  val metaVarInstRes = Map(
    1 -> Map(
      1 -> λ(o)(|||((1,o), mkMetaVar(o, 1))).betaNormalize,
      2 -> λ(o)(|||((1,o), LitTrue)).betaNormalize,
      3 -> λ(o)(|||((1,o), LitFalse)).betaNormalize,
      4 -> λ(o)(|||((1,o), mkMetaVar(o, 1))).betaNormalize,
      5 -> λ(o)(|||((1,o), mkMetaVar(o, 2))).betaNormalize
    ),
    2 -> Map(
      1 -> &(Forall(λ(o)(|||((1,o),Not(mkMetaVar(o,1))))), mkMetaVar(o,2)).betaNormalize,
      2 -> &(Forall(λ(o)(|||((1,o),Not(LitTrue)))), mkMetaVar(o,2)).betaNormalize,
      3 -> &(Forall(λ(o)(|||((1,o),Not(LitFalse)))), LitTrue).betaNormalize,
      4 -> &(Forall(λ(o)(|||((1,o),Not(mkMetaVar(o,1))))), LitTrue).betaNormalize,
      5 -> &(Forall(λ(o)(|||((1,o),Not(mkMetaVar(o,2))))), LitTrue).betaNormalize
    )
  )

  for (t <- metaVarInstTestTerms) {
    for (s <- metaVarInstTestSubst) {
      test(s"Meta-variable instantiation test ${t._1}/${s._1}") {
        val term = t._2
        val subst = s._2
        println(s"Instantiate ${term.pretty} with ${subst.pretty}")
        val inst = term.substitute(subst).betaNormalize
        assertResult(metaVarInstRes(t._1)(s._1))(inst)
      }
    }
  }
}


class TermNormalizationTestSuite extends LeoTestSuite {

  import impl.Signature
  import Term._
  import leo.Checked

  test("etaExpand - all binders of type i", Checked) {
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a", (s.i->:s.i)->:s.i))
    val t = Term.λ(s.i)(Term.mkTermApp(a,Term.mkTermApp(Term.mkMetaVar(Type.mkFunType(s.i,s.i->:s.i), 1), Term.mkBound(s.i,1))))
    val m = Term.λ(s.i)(Term.mkTermApp(a,Term.λ(s.i)(Term.mkTermApp(
      Term.mkMetaVar(Type.mkFunType(s.i,s.i->:s.i), 1), List(Term.mkBound(s.i,2), Term.mkBound(s.i,1))))))
    assert(m.equals(t.etaExpand))
  }

  test("etaExpand - the two binders of different type", Checked) {
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a", ((s.i->:s.i)->:s.i)->:s.i))
    println("type of a: " + a.ty.pretty)
    val y = Term.mkMetaVar(Type.mkFunType(s.i,(s.i->:s.i)->:s.i), 1)
    println("type of sV1: " + y.ty.pretty)
    val t = Term.λ(s.i)(Term.mkTermApp(a,Term.mkTermApp(y,
      Term.mkBound(s.i,1))))
    println("type of t: " + t.ty.pretty)
    println("t: " + t.pretty)
    println("is t typed properly? " + t.typeCheck)
    println("t.etaExpand: " + t.etaExpand.pretty)
    println("type of t.etaExpand: " + t.etaExpand.ty.pretty)
    println("is t.etaExpand typed properly? " + t.etaExpand.typeCheck + " - really?")

    val m = Term.λ(s.i)(Term.mkTermApp(a,Term.λ(s.i->:s.i)(Term.mkTermApp(
      y, List(Term.mkBound(s.i,2), Term.mkBound(s.i,1))))))
    println("the expected t.etaExpand: " + m.pretty)
    println("weird: when applying etaExpand to the above: " + m.etaExpand.pretty)
    assert(m.equals(t.etaExpand))
  }
}
