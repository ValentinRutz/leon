package leon.synthesis.condabd
package evaluation

import scala.collection.mutable.ArrayBuffer

import leon._
import leon.evaluators._
import leon.evaluators.EvaluationResults._
import leon.purescala.Trees._
import leon.purescala.Definitions.{ TypedFunDef, ValDef, Program, ModuleDef }
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps

import examples._
import ranking._

import _root_.insynth.util.logging.HasLogger

case class DefaultExampleRunner(program: Program, tfd: TypedFunDef, ctx: LeonContext,
  candidates: Seq[Candidate], inputExamples: Seq[Example],
  maxSteps: Int = 2000) extends ExampleRunner(inputExamples) with HasLogger {

  private var _examples = ArrayBuffer(inputExamples.map(_.map): _*)
    
  override def addExamples(newExamples: Seq[Example]) = {
    super.addExamples(newExamples)
    _examples ++= newExamples.map(_.map)
  }

  val evaluationContext = ctx
  
  lazy val _evaluator = new DefaultEvaluator(evaluationContext, program)
  override def getEvaluator = _evaluator
  
  override def evaluate(expr: Expr, mapping: Map[Identifier, Expr]): Boolean = {
    finest("to evaluate: " + expr + " for mapping: " + mapping)
    getEvaluator.eval(expr, mapping) match {
      case Successful(BooleanLiteral(true)) =>
        finest("Eval succeded: EvaluationSuccessful(true)")
        true
      case m =>
        finest("Eval failed: " + m)
        false
    }
  }
  
  def evaluate(expr: Expr, args: Seq[Expr]): Boolean = {
    evaluate(expr, tfd.params.map(_.id).zip(args).toMap)
  }

  override def evaluateToResult(expr: Expr, mapping: Map[Identifier, Expr]) = {
    finest("to evaluate: " + expr + " for mapping: " + mapping)
    getEvaluator.eval(expr, mapping)
  }

  
  /** if the example runner knows about candidates and input examples, run by their indexes */
  def evaluate(candidateInd: Int, exampleInd: Int) =
    evaluate(candidates(candidateInd).prepareExpression, _examples(exampleInd))
  
  /** filter counterexamples according to an expression (precondition) */
  def filter(prec: Expr) = {
    entering("filter(" + prec + ")")
    finest("Old counterExamples.size: " + examples.size)
        
    val (newTransformed, newExamples) = ((_examples zip examples) filter {
      case ((exMap, _)) =>
      	evaluate(prec, exMap)
    }).unzip
     
    _examples = newTransformed
    examples = newExamples
    
    finest("New counterExamples.size: " + examples.size)
  }

  /** count how many examples pass */
  def countPassed(expressionToCheck: Expr) = {
    finest("count passed for expression to check: " + expressionToCheck)

    val (passed, failed) = examples.partition(
      ex => evaluate(expressionToCheck, ex.map)
    )
    
    (passed.size, passed)
  }

}
