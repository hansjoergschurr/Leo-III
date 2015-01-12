package leo
package agents
package impl

import leo.datastructures.{Role_Plain, Clause}
import leo.datastructures.blackboard.{Store, FormulaEvent, FormulaStore, Event}
import leo.modules.proofCalculi.resolution.Clausification

object ClausificationAgent {
  def apply() : Unit = (new ClausificationAgent()).register()
}

/**
 * Performs stepwise clausification on the Clauses of the Blackboard.
 *
 * @author Max Wisniewski
 * @since 12/1/15
 */
class ClausificationAgent extends PriorityAgent{
  /**
   * Internal method called from the filter method. Specific to the agent.
   *
   * @param event - The event that triggered the filter
   * @return A sequence of new tasks, to be added to the internal priority queue.
   */
  override protected def toFilter(event: Event): Iterable[Task] = event match {
    case FormulaEvent(f) =>
      val nc = Clausification.clausify(f.clause)
      return List(ClausificationTask(f,nc))
    case _ => return Nil
  }

  /**
   * Each task can define a maximum amount of money, they
   * want to posses.
   *
   * A process has to be careful with this barrier, for he
   * may never be doing anything if he has to low money.
   *
   * @return maxMoney
   */
  override def maxMoney: Double = 7000

  /**
   *
   * @return the name of the agent
   */
  override def name: String = "ClausificationAgent"

  /**
   * This function runs the specific agent on the registered Blackboard.
   */
  override def run(t: Task): Result = t match {
    case ClausificationTask(dc, nc) =>
      val nf = nc map {c => dc.randomName().newClause(c).newRole(Role_Plain)}
      return new StdResult(nf.toSet, Map.empty, Set(dc))
    case _ =>
      Out.warn(s"$name: Got a wrong task to execute")
      return EmptyResult
  }
}


private class ClausificationTask(val dc : FormulaStore, val nc : Seq[Clause]) extends Task{
  override def readSet(): Set[FormulaStore] = Set.empty
  override def writeSet(): Set[FormulaStore] = Set(dc)
  override def bid(budget: Double): Double = budget / 20

  override def toString() : String = s"Clausify: ${dc.pretty} => [${nc.map(_.pretty).mkString(", ")}}]"
}

object ClausificationTask {
  /**
   * Creates a Clausification task with `dc` the old FormulaStore to be deleted and `nc` the list
   * of new clauses to be inserted into the blackboard.
   * @param dc - Old Formula Store
   * @param nc - List of new clauses
   * @return A Clausification Task
   */
  def apply(dc : FormulaStore, nc : Seq[Clause]) : Task = new ClausificationTask(dc, nc)

  def unapply(t : Task) : Option[(FormulaStore, Seq[Clause])] = t match {
    case t : ClausificationTask => Some(t.dc, t.nc)
    case _ => None
  }
}
