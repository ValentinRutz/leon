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

class OneStepEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog) {
  override val name = "one-step evaluator"
  override val description = "One-step interpreter for PureScala expressions"

  type RC = DefaultRecContext
  type GC = DefaultGlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC = new DefaultGlobalContext(false, stepsLeft = -1)

  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def withNewVar(id: Identifier, v: Expr) = copy(mappings + (id -> v))

    def withVars(news: Map[Identifier, Expr]) = copy(news)
  }

  class DefaultGlobalContext(var madeStep: Boolean, stepsLeft: Int) extends GlobalContext(stepsLeft) { }


  def le(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    if (gctx.madeStep) {
      expr
    } else {
      e(expr)
    }
  }

  def hasMadeStep(implicit gctx: GC) = {
    gctx.madeStep
  }

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    val res = expr match {
      case Variable(id) =>
        rctx.mappings.get(id) match {
          case Some(v) => v
          case None =>
            throw EvalError("No value for identifier " + id.name + " in mapping.")
        }

      case Tuple(ts) =>
        val tsRec = ts.map(le)
        Tuple(tsRec)

      case TupleSelect(t, i) =>
        le(t) match {
          case Tuple(ts) =>
            ts(i-1)
          case r =>
            r
        }

      case Let(i,ex,b) =>
        if (isLiteral(ex)) {
          replace(Map(Variable(i) -> ex), b)
        } else {
          Let(i, le(ex), b)
        }

      case FunctionInvocation(tfd, args) =>
        if (args.forall(isLiteral) && tfd.hasBody) {
          val argsMap = (tfd.params.map(_.id) zip args).toMap

          replaceFromIDs(argsMap, tfd.body.get)
        } else {
          FunctionInvocation(tfd, args.map(le))
        }

      case IfExpr(cond, thenn, elze) =>
        cond match {
          case BooleanLiteral(true) =>
            thenn

          case BooleanLiteral(false) =>
            elze

          case _ =>
            IfExpr(le(cond), thenn, elze)
        }

      case And(args) =>
        args.head match {
          case BooleanLiteral(false) =>
            BooleanLiteral(false)

          case BooleanLiteral(true) =>
            if(args.size == 1) {
              BooleanLiteral(true)
            } else {
              And(args.tail)
            }
          case other =>
            And(le(other) +: args.tail)
        }

      case Or(args) =>
        args.head match {
          case BooleanLiteral(true) =>
            BooleanLiteral(true)
          case BooleanLiteral(false) =>
            if(args.size == 1) {
              BooleanLiteral(false)
            } else {
              Or(args.tail)
            }
          case other =>
            Or(le(other) +: args.tail)
        }

      case Not(arg) =>
        arg match {
          case BooleanLiteral(v) => BooleanLiteral(!v)
          case other =>
            Not(le(other))
        }

      case Implies(l,r) =>
        (l, r) match {
          case (BooleanLiteral(b1), BooleanLiteral(b2)) => BooleanLiteral(!b1 || b2)
          case (l, r) =>
            Implies(le(l), le(r))
        }

      case Iff(l,r) =>
        (l, r) match {
          case (BooleanLiteral(b1), BooleanLiteral(b2)) => BooleanLiteral(b1 == b2)
          case (l, r) =>
            Iff(le(l), le(r))
        }

      case Equals(l, r) =>
        (l, r) match {
          case (FiniteSet(el1), FiniteSet(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
          case (FiniteMap(el1), FiniteMap(el2)) => BooleanLiteral(el1.toSet == el2.toSet)
          case (l, r) if isLiteral(l) && isLiteral(r) => BooleanLiteral(l == r)
          case _ => Equals(le(l), le(r))
        }

      case CaseClass(cd, args) =>
        CaseClass(cd, args.map(le(_)))

      case CaseClassInstanceOf(cct, expr) =>
        expr match {
          case CaseClass(ct2, _) => BooleanLiteral(ct2 == cct)
          case _ => CaseClassInstanceOf(cct, le(expr))
        }

      case CaseClassSelector(ct1, expr, sel) =>
        expr match {
          case CaseClass(ct2, args) if ct1 == ct2 => args(ct1.classDef.selectorID2Index(sel))
          case _ =>
            CaseClassSelector(ct1, le(expr), sel)
        }

      case Plus(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
          case (l, r) => Plus(le(l), le(r))
        }

      case Minus(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
          case (l, r) => Minus(le(l), le(r))
        }

      case UMinus(ex) =>
        ex match {
          case IntLiteral(i) => IntLiteral(-i)
          case r => UMinus(le(ex))
        }

      case Times(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
          case (l, r) => Times(le(l), le(r))
        }

      case Division(l,r) =>
        (l, r) match {
          case (_, IntLiteral(i2)) if i2 == 0 => Error("Division by 0")
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 / i2)
          case (l, r) => Division(le(l), le(r))
        }

      case Modulo(l,r) =>
        (l, r) match {
          case (_, IntLiteral(i2)) if i2 == 0 => Error("Modulo by 0")
          case (IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 % i2)
          case (l, r) => Modulo(le(l), le(r))
        }

      case LessThan(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
          case (l, r) => LessThan(le(l), le(r))
        }

      case GreaterThan(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
          case (l, r) => GreaterThan(le(l), le(r))
        }

      case LessEquals(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
          case (l, r) => LessEquals(le(l), le(r))
        }

      case GreaterEquals(l,r) =>
        (l, r) match {
          case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
          case (l, r) => GreaterEquals(le(l), le(r))
        }

      case e => e

      /*
      case FunctionInvocation(tfd, args) =>
        if (gctx.stepsLeft < 0) {
          throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
        }
        gctx.stepsLeft -= 1

        val evArgs = args.map(a => e(a))

        // build a mapping for the function...
        val frame = rctx.withVars((tfd.params.map(_.id) zip evArgs).toMap)
        
        if(tfd.hasPrecondition) {
          e(matchToIfThenElse(tfd.precondition.get))(frame, gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) =>
              throw RuntimeError("Precondition violation for " + tfd.id.name + " reached in evaluation.: " + tfd.precondition.get)
            case other => throw RuntimeError(typeErrorMsg(other, BooleanType))
          }
        }

        if(!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) {
          throw EvalError("Evaluation of function with unknown implementation.")
        }

        val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
        val callResult = e(matchToIfThenElse(body))(frame, gctx)

        if(tfd.hasPostcondition) {
          val (id, post) = tfd.postcondition.get

          val freshResID = FreshIdentifier("result").setType(tfd.returnType)
          val postBody = replace(Map(Variable(id) -> Variable(freshResID)), matchToIfThenElse(post))

          e(matchToIfThenElse(post))(frame.withNewVar(id, callResult), gctx) match {
            case BooleanLiteral(true) =>
            case BooleanLiteral(false) => throw RuntimeError("Postcondition violation for " + tfd.id.name + " reached in evaluation.")
            case other => throw EvalError(typeErrorMsg(other, BooleanType))
          }
        }

        callResult

      case SetUnion(s1,s2) =>
        (e(s1), e(s2)) match {
          case (f@FiniteSet(els1),FiniteSet(els2)) => FiniteSet((els1 ++ els2).distinct).setType(f.getType)
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }

      case SetIntersection(s1,s2) =>
        (e(s1), e(s2)) match {
          case (f @ FiniteSet(els1), FiniteSet(els2)) => {
            val newElems = (els1.toSet intersect els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            FiniteSet(newElems).setType(f.getType)
          }
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }

      case SetDifference(s1,s2) =>
        (e(s1), e(s2)) match {
          case (f @ FiniteSet(els1),FiniteSet(els2)) => {
            val newElems = (els1.toSet -- els2.toSet).toSeq
            val baseType = f.getType.asInstanceOf[SetType].base
            FiniteSet(newElems).setType(f.getType)
          }
          case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
        }

      case ElementOfSet(el,s) => (e(el), e(s)) match {
        case (e, f @ FiniteSet(els)) => BooleanLiteral(els.contains(e))
        case (l,r) => throw EvalError(typeErrorMsg(r, SetType(l.getType)))
      }
      case SubsetOf(s1,s2) => (e(s1), e(s2)) match {
        case (f@FiniteSet(els1),FiniteSet(els2)) => BooleanLiteral(els1.toSet.subsetOf(els2.toSet))
        case (le,re) => throw EvalError(typeErrorMsg(le, s1.getType))
      }
      case SetCardinality(s) =>
        val sr = e(s)
        sr match {
          case FiniteSet(els) => IntLiteral(els.size)
          case _ => throw EvalError(typeErrorMsg(sr, SetType(AnyType)))
        }

      case f @ FiniteSet(els) => FiniteSet(els.map(e(_)).distinct).setType(f.getType)

      case other =>
        context.reporter.error("Error: don't know how to handle " + other + " in Evaluator.")
        throw EvalError("Unhandled case in Evaluator : " + other) 
        */
    }
    if (res != expr) {
      gctx.madeStep = true
    }
    res
  }

  def isLiteral(e: Expr): Boolean = e match {
    case Variable(_) => false
    case Tuple(ts) =>
      ts.forall(isLiteral)

    case CaseClass(cct, args) =>
      args.forall(isLiteral)

    case t: Terminal =>
      true

    case _ =>
      false
  }
}
