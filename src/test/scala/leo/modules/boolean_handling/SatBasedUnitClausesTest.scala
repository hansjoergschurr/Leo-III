package leo.modules.boolean_handling

import leo.{Checked, LeoTestSuite}
import leo.datastructures.{Term, Signature}
import leo.modules.HOLSignature.{&, i, o, |||}

import scala.collection.immutable.HashMap
/**
  * Created by Hans-Jörg Schurr on 12/2/16.
  */
class SatBasedUnitClausesTest extends LeoTestSuite  {

  def freshTerms(implicit s : Signature) : Array[Term] = {
    Array.range(1, 11).map((x : Int) => Term.mkAtom(s.addUninterpreted(x.toString, o)))
  }

  test("Equality Graph: Add edges", Checked){
    implicit val s = getFreshSignature
    val terms = freshTerms(s)

    var graph  = EqualityGraph(terms.toSet, HashMap.empty)
    assertResult(0)(graph.edges.size)
    graph  = graph.addEdge(terms(0), terms(1))
    assertResult(2)(graph.edges.size)
    assertResult(1)(graph.edges.get(terms(0)).size)
    assertResult(1)(graph.edges.get(terms(1)).size)
    assert(graph.edges (terms(0)).contains(terms(1)))
    assert(graph.edges (terms(1)).contains(terms(0)))
    assert(graph.neighbors(terms(0)).contains(terms(1)))
    assert(graph.neighbors(terms(1)).contains(terms(0)))
  }

  test("Equality Graph: Iterate constraints of triangle", Checked) {
    implicit val s = getFreshSignature
    val terms = freshTerms(s)

    var graph  = EqualityGraph(terms.toSet, HashMap.empty)
    assertResult(0)(graph.edges.size)
    graph = graph.addEdge(terms(0), terms(1))
    graph = graph.addEdge(terms(1), terms(2))
    graph = graph.addEdge(terms(2), terms(0))

    val const = graph.constraints
    assertResult(3)(const.size)
    assert(const.contains((terms(0),terms(2), terms(1))))
    assert(const.contains((terms(1),terms(2), terms(0))))
    assert(const.contains((terms(2),terms(1), terms(0))))
  }

  test("Equality Graph: Delete Node", Checked) {
    implicit val s = getFreshSignature
    val terms = freshTerms(s)

    var graph  = EqualityGraph(terms.toSet, HashMap.empty)
    graph = graph.addEdge(terms(0), terms(1))
    graph = graph.addEdge(terms(1), terms(2))
    graph = graph.addEdge(terms(2), terms(0))

    graph = graph.deleteNode(terms(0))
    assertResult(10-1)(graph.nodes.size)
    assertResult(false)(graph.nodes.contains(terms(0)))
    assertResult(false)(graph.neighbors(terms(1)).contains(terms(0)))
    assertResult(false)(graph.neighbors(terms(2)).contains(terms(0)))
  }

  test("Equality Graph: Make chordal", Checked) {
    implicit val s = getFreshSignature
    val terms = freshTerms(s)

    var graph  = EqualityGraph(terms.toSet, HashMap.empty)
    graph = graph.addEdge(terms(0), terms(1))
    graph = graph.addEdge(terms(1), terms(2))
    graph = graph.addEdge(terms(2), terms(3))
    graph = graph.addEdge(terms(3), terms(0))

    assertResult(10)(graph.nodes.size)
    // This is a hack: constraints is not well defined on none-chordal graphs.
    assertResult(0)(graph.constraints.size)

    graph = graph.chordal
    assertResult(10)(graph.nodes.size)
    assertResult(6)(graph.constraints.size)

  }
}
