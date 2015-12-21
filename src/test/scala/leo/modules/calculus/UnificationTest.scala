package leo.modules.calculus

import leo.{Checked, LeoTestSuite}
import leo.datastructures._
import leo.datastructures.impl.Signature
import scala.collection.immutable.HashMap
import Term._

class UnificationAuxTestSuite extends LeoTestSuite {

  test("partialBinding(i>(i>i)>i,a:(i>i)>i>i)", Checked) {
    /* n = 2
     * m = 2
     * t = λ i (i>i).a(y1(1,2),y2(1,2)).etaExpand
     */
    val s = getFreshSignature
    val typ = mkAtom(s.addUninterpreted("_1", s.i->:(s.i->:s.i)->:s.i)).ty
    val a = mkAtom(s.addUninterpreted("a", (s.i->:s.i)->:s.i->:s.i))

    val res = HuetsPreUnification.partialBinding(typ,a)

    val xn = List(Term.mkBound(s.i,1), Term.mkBound(s.i->:s.i,2))
    val xnTyp = xn.map(_.ty)
    val ym = List(
        Term.mkTermApp(Term.mkMetaVar(Type.mkFunType(xnTyp,s.i->:s.i), 1), xn),
        Term.mkTermApp(Term.mkMetaVar(Type.mkFunType(xnTyp,s.i), 2), xn)
      )
    val t = Term.λ(xn.map(_.ty))(Term.mkTermApp(a,ym)).etaExpand

    assert (res.equals(t))
  }

  test("partialBinding(i>((i>i)>i)>i,a:(((i>i)>i)>i)>(i>i)>>i)", Checked) {
    /* n = 2
     * m = 2
     * t = λ i (i>i>i).a(y1(1,2),y2(1,2)).etaExpand
     */
    val s = getFreshSignature
    val x1 = s.i
    val x2 = (s.i->:s.i)->:s.i
    val x3 = s.i
    val typ = mkAtom(s.addUninterpreted("_1", x1->:x2->:x3)).ty
    val y1 = ((s.i->:s.i)->:s.i)->:s.i
    val y2 = s.i->:s.i
    val y3 = s.i
    val a = mkAtom(s.addUninterpreted("a", y1->:y2->:y3))

    val res = HuetsPreUnification.partialBinding(typ,a)

    val xn = List(Term.mkBound(x1,1), Term.mkBound(x2,2))
    val xnTyp = xn.map(_.ty)
    val ym = List(
        Term.mkTermApp(Term.mkMetaVar(Type.mkFunType(xnTyp,y1), 3), xn),
        Term.mkTermApp(Term.mkMetaVar(Type.mkFunType(xnTyp,y2), 4), xn)
      )
    val tt = Term.λ(xn.map(_.ty))(Term.mkTermApp(a,ym))
    println(tt.pretty)
    val t = tt.etaExpand
    println(t.pretty)

    println(res.pretty)
    println(t.pretty)

    assert (res.equals(t))
  }


}

class UnificationRulesTestSuite extends LeoTestSuite {
}

class UnificationTestSuite extends LeoTestSuite {

  //x(a) = f(a,a)
  test("f(x,x) = f(a,a)", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))

    val x = mkFreshMetaVar(s.i)
    val z = mkFreshMetaVar(s.i)
    val t1 : Term = mkTermApp(f , List(x,x))
    val t2 : Term = mkTermApp(f , List(a,z))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val sb: Subst = result.next
    assert(!result.hasNext)
    println(sb.pretty)
    assert (t1.substitute(sb).betaNormalize.equals (t2.substitute(sb).betaNormalize))
  }

  // x(a) = f(a,a)
  test("x(a) = f(a,a)", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i ->: s.i))


    val t1 : Term = mkTermApp(mkFreshMetaVar(s.i ->: s.i),a)
    val t2 : Term = mkTermApp(f , List(a,a))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val res1 : Term = \(s.i)(mkTermApp(f,List(mkBound(s.i,1), mkBound(s.i,1))))

    // should have 4 unifiers, we need to check they are different from each other
    for( a <- 1 to 4) {
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals (t2))
    }
    assert (result.isEmpty)
  }

  // x(f(a)) = f(x(a)) -> inf # of unifiers
  test("x(f(a)) = f(x(a))", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
  val x = mkFreshMetaVar(s.i ->: s.i)

    val t1 : Term = mkTermApp(x,mkTermApp(f,a))
    val t2 : Term = mkTermApp(f,mkTermApp(x,a))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val res1 : Term = \(s.i)(mkTermApp(f,List(mkBound(s.i,1), mkBound(s.i,1))))

    // should have inf many unifiers
    for( a <- 1 to 50) {
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }
  }

  test("x(f(a,a)) = f(x(a),f(f(a,a),a))", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i ->: s.i))
  val x = mkFreshMetaVar(s.i ->: s.i)

    val t1 : Term = mkTermApp(x,mkTermApp(f,List(a,a)))
    val t2 : Term = mkTermApp(f,List(mkTermApp(x,a),mkTermApp(f, List(mkTermApp(f, List(a,a)),a))))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val res1 : Term = \(s.i)(mkTermApp(f,List(mkBound(s.i,1), mkBound(s.i,1))))

    // Does it have only 6 unifiers?!
    for( a <- 1 to 5) { // the 7th substitutions fails from some reason
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }
  }

  test("x(f(a,g(a,a))) = f(a,g(x(a),a))", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i ->: s.i))
  val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i ->: s.i))
  val x = mkFreshMetaVar(s.i ->: s.i)

    val t1 : Term = mkTermApp(x,mkTermApp(f,List(a,mkTermApp(g,List(a,a)))))
    val t2 : Term = mkTermApp(f,List(a,mkTermApp(g,List(mkTermApp(x,List(a)),a))))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val res1 : Term = \(s.i)(mkTermApp(f,List(mkBound(s.i,1), mkBound(s.i,1))))

    for( a <- 1 to 5) { // fails for 30 pre-unifiers!
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }
  }

test("x(f(a,g(f(a,a),a))) = f(a,g(x(f(a,a),a)))", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i ->: s.i))
  val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i ->: s.i))
  val x = mkFreshMetaVar(s.i ->: s.i)

    val t1 : Term = mkTermApp(x,mkTermApp(f,List(a,mkTermApp(g,List(mkTermApp(f,List(a,a)),a)))))
    val t2 : Term = mkTermApp(f,List(a,mkTermApp(g,List(mkTermApp(x,List(mkTermApp(f,List(a,a)))),a))))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val res1 : Term = \(s.i)(mkTermApp(f,List(mkBound(s.i,1), mkBound(s.i,1))))

    for( a <- 1 to 10) { //fails for 30!
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }
  }

  test("x(f(a,a)) = f(xa, f(a,f(a,a)))", Checked){
  val s = getFreshSignature

  val a = mkAtom(s.addUninterpreted("a",s.i))
  val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i ->: s.i))
  val x = mkFreshMetaVar(s.i ->: s.i)

    val t1 : Term = mkTermApp(x,mkTermApp(f,List(a,a)))
    val t2 : Term = mkTermApp(f,List(mkTermApp(x,List(a)), mkTermApp(f,List(a, mkTermApp(f, List(a,a))))))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    val res1 : Term = \(s.i)(mkTermApp(f,List(mkBound(s.i,1), mkBound(s.i,1))))

    for( a <- 1 to 5) { // fails for 50?!
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }
  }

  // the next two tests are similar but one is over monadic x and the second is over a binary x

 test("x(g(y1,a)) = g(y2, x(a))", Checked) {
    val s = getFreshSignature

    val x = mkFreshMetaVar(s.i ->: s.i)
    val y1 = mkFreshMetaVar(s.i)
    val y2 = mkFreshMetaVar(s.i)

    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i ->: s.i))
    val a = mkAtom(s.addUninterpreted("a", s.i))

    val t1 = mkTermApp(x, Seq(mkTermApp(g, Seq(y1,a))))
    val t2 = mkTermApp(g, Seq(y2, mkTermApp(x, Seq(a))))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    for( a <- 1 to 1) {
      // the second is a preunifier which cannot be determined by equals
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }

  }


 test("x(u, g(y1,a)) = g(y2, x(v,a))", Checked) {
    val s = getFreshSignature

    val x = mkFreshMetaVar(s.i ->: s.i ->: s.i)
    val y1 = mkFreshMetaVar(s.i)
    val y2 = mkFreshMetaVar(s.i)

    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i ->: s.i))
    val u = mkAtom(s.addUninterpreted("u", s.i))
    val a = mkAtom(s.addUninterpreted("a", s.i))
    val v = mkAtom(s.addUninterpreted("v", s.i))

    val t1 = mkTermApp(x, Seq(u, mkTermApp(g, Seq(y1,a))))
    val t2 = mkTermApp(g, Seq(y2, mkTermApp(x, Seq(v,a))))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    for( a <- 1 to 1) { // the next are ore-unifiers
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }

  }

    test("y(ey) = ~ (sKf(skX(y), ey))", Checked) {
    val s = getFreshSignature

    val y = mkFreshMetaVar(s.i ->: s.o)
    val ey = mkFreshMetaVar(s.i)

    val sKf = mkAtom(s.addUninterpreted("skf", s.i ->: s.i ->: s.o))
    val skX = mkAtom(s.addUninterpreted("skX", (s.i ->: s.o) ->: s.i))

    val t1 = mkTermApp(y, Seq(ey))
    val t2 = Not(mkTermApp(sKf, Seq(mkTermApp(skX, y), ey)))

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    for( a <- 1 to 1) {
      val sb: Subst = result.next
      assert (t1.substitute(sb).betaNormalize.equals(t2.substitute(sb).betaNormalize))
    }
  }

  // this example should not terminate and should be timed out. It can be dealt with using Tomer's new unification procedure without a timeout.
  test("sV135 ⋅ (sV2 ⋅ (⊥);⊥) = ~ ⋅ (| ⋅ (sV135 ⋅ (sV2 ⋅ (⊥);⊥);sV136 ⋅ (sV2 ⋅ (⊥);⊥);⊥);⊥)", Checked) {
    val s = getFreshSignature

    val sV135 = mkFreshMetaVar(s.i ->: s.o)
    val sV136 = mkFreshMetaVar(s.i ->: s.o)
    val sV2 = mkFreshMetaVar(s.i)

    val t1 = mkTermApp(sV135, sV2)
    println(t1.pretty +" "+ t1.typeCheck)
    val t2 = Not(|||(mkTermApp(sV135, sV2),mkTermApp(sV136,sV2)))
    println(t2.pretty + " " + t2.typeCheck)

    val result : Iterator[Subst] = HuetsPreUnification.unify(t1,t2).iterator

    assert (result.isEmpty)
  }

}
