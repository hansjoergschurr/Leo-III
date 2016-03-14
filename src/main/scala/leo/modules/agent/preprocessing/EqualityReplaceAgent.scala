package leo.modules.agent.preprocessing

import leo.agents.{TAgent, Task, Agent}
import leo.datastructures.ClauseAnnotation.InferredFrom
import leo.datastructures.{Clause, Term, Type, ClauseProxy}
import leo.datastructures.blackboard._
import leo.datastructures.context.Context
import leo.modules.seqpproc.{ReplaceAndrewsEq, ReplaceLeibnizEq}

/**
  * Created by mwisnie on 3/7/16.
  */
object EqualityReplaceAgent extends Agent{
  override def name: String = "equality_replace_agent"
  override val interest = Some(Seq(ClauseType))
  override def filter(event: Event): Iterable[Task] = event match {
    case DataEvent(cl : ClauseProxy, ClauseType) => commonFilter(cl, Context())
    case DataEvent((cl : ClauseProxy, c : Context), ClauseType) => commonFilter(cl, c)
    case _ => Seq()
  }

  private def commonFilter(cl : ClauseProxy, c : Context) : Iterable[Task] = {
    val (can1, map) = ReplaceLeibnizEq.canApply(cl.cl)
    if(can1){
      Seq(new LeibnitzEQTask(cl, cl.cl, map, c, this))
    } else {
      val (can2, map2) = ReplaceAndrewsEq.canApply(cl.cl)
      if(can2){
        Seq(new AndrewEQTask(cl, cl.cl, map2, c, this))
      } else {
        Seq()
      }
    }
  }
}

abstract class EqualityReplaceTask(cl : ClauseProxy, a : TAgent) extends Task {
  override def name: String = "equality_replace_task"
  override def getAgent: TAgent = a
  override def writeSet(): Map[DataType, Set[Any]] = Map(ClauseType -> Set(cl))
  override def readSet(): Map[DataType, Set[Any]] = Map()
  override def bid: Double = 0.1
  override def pretty: String = s"equality_replace_task(${cl.cl.pretty})"
}

/**
  * Replaces Leibnitzequality and then andrew equality.
  */
class LeibnitzEQTask(cl : ClauseProxy, clause : Clause, map : Map[Int, Term], c : Context, a : TAgent) extends EqualityReplaceTask(cl, a){
  override def run: Result = {
    val (nc, _) = ReplaceLeibnizEq(clause, map)
    val (can, map2) = ReplaceAndrewsEq.canApply(nc)
    val fc = if(can){
      ReplaceAndrewsEq(nc, map2)._1
    } else {
      nc
    }
    Result().update(ClauseType)((cl, c))((Store(fc, cl.role, c, InferredFrom(ReplaceAndrewsEq, cl)), c))
  }
}

/**
  * Replaces only Andrew Equality
  */
class AndrewEQTask(cl : ClauseProxy, clause : Clause, map : Map[Int, Type], c : Context, a : TAgent) extends EqualityReplaceTask(cl, a){
  override def run: Result = {
    val (nc, _) = ReplaceAndrewsEq(clause, map)
    Result().update(ClauseType)((cl, c))((Store(nc, cl.role, c, InferredFrom(ReplaceAndrewsEq, cl)), c))
  }
}