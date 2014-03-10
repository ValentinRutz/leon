/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._

import solvers.TimeoutSolver

import xlang.Trees._

class LastStepEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog) {
  override val name = "last-step evaluator"
  override val description = "Last-step interpreter for PureScala expressions"

  type RC = DefaultRecContext
  type GC = DefaultGlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC = new DefaultGlobalContext(false, stepsLeft = -1)

  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def withNewVar(id: Identifier, v: Expr) = copy(mappings + (id -> v))

    def withVars(news: Map[Identifier, Expr]) = copy(news)
  }

  class DefaultGlobalContext(var madeStep: Boolean, stepsLeft: Int) extends GlobalContext(stepsLeft) { }

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case ex if expr.hasPreviousState => expr.previousState.get
    case ex => ex
  }
}
