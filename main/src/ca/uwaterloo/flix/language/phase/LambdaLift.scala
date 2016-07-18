/*
 * Copyright 2015-2016 Ming-Ho Yee
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.language.ast.Name.Ident
import ca.uwaterloo.flix.language.ast.SimplifiedAst.Expression
import ca.uwaterloo.flix.language.ast.{Ast, Name, SimplifiedAst, SourceLocation, Symbol, Type}
import ca.uwaterloo.flix.util.InternalCompilerException

import scala.collection.mutable

object LambdaLift {

  /**
    * Mutable map of top level definitions.
    */
  private type TopLevel = mutable.Map[Symbol.Resolved, SimplifiedAst.Definition.Constant]

  /**
    * Performs lambda lifting on all definitions in the AST.
    */
  def lift(root: SimplifiedAst.Root)(implicit genSym: GenSym): SimplifiedAst.Root = {
    val t = System.nanoTime()

    // A mutable map to hold lambdas that are lifted to the top level.
    val m: TopLevel = mutable.Map.empty

    val definitions = root.constants.map {
      case (name, decl) => name -> lift(decl, m)
    }
    val properties = root.properties.map(p => lift(p, m))
    val facts = root.facts.map(f => lift(f, m))
    val rules = root.rules.map(r => lift(r, m))

    // Return the updated AST root.
    val e = System.nanoTime() - t
    root.copy(constants = definitions ++ m, properties = properties, facts = facts, rules = rules, time = root.time.copy(lambdaLift = e))
  }

  /**
    * Performs lambda lifting on the given declaration `decl`.
    *
    * The definition's expression is closure converted, and then lifted definitions are added to the mutable map `m`.
    * The updated definition is then returned.
    */
  private def lift(decl: SimplifiedAst.Definition.Constant, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Definition.Constant = {
    val convExp = ClosureConv.convert(decl.exp)
    val liftExp = lift(convExp, decl.name.parts, m)
    decl.copy(exp = liftExp)
  }

  /**
    * Performs lambda lifting on the given property `prop`.
    *
    * The property's expression is closure converted, and then the lifted definitions are added to the mutable map `m`.
    * The updated definition is then returned.
    */
  private def lift(prop: SimplifiedAst.Property, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Property = {
    val convExp = ClosureConv.convert(prop.exp)
    val liftExp = lift(convExp, List(prop.law.toString), m)
    prop.copy(exp = liftExp)
  }

  /**
    * Performs lambda lifting on the given expression `exp0`.
    *
    * Adds new top-level definitions to the mutable map `m`.
    */
  private def lift(exp0: Expression, nameHint: List[String], m: TopLevel)(implicit genSym: GenSym): Expression = {
    def visit(e: Expression): Expression = e match {
      case Expression.Unit => e
      case Expression.True => e
      case Expression.False => e
      case Expression.Char(lit) => e
      case Expression.Float32(lit) => e
      case Expression.Float64(lit) => e
      case Expression.Int8(lit) => e
      case Expression.Int16(lit) => e
      case Expression.Int32(lit) => e
      case Expression.Int64(lit) => e
      case Expression.BigInt(lit) => e
      case Expression.Str(lit) => e
      case Expression.LoadBool(n, o) => e
      case Expression.LoadInt8(b, o) => e
      case Expression.LoadInt16(b, o) => e
      case Expression.LoadInt32(b, o) => e
      case Expression.StoreBool(b, o, v) => e
      case Expression.StoreInt8(b, o, v) => e
      case Expression.StoreInt16(b, o, v) => e
      case Expression.StoreInt32(b, o, v) => e
      case Expression.Var(ident, o, tpe, loc) => e
      case Expression.Ref(name, tpe, loc) => e

      case Expression.Lambda(args, body, tpe, loc) =>
        // Lift the lambda to a top-level definition, and replacing the Lambda expression with a Ref.

        // First, recursively visit the lambda body, lifting any inner lambdas.
        val exp = visit(body)

        // Then, generate a fresh name for the lifted lambda.
        val name = genSym.freshDefn(nameHint)

        // Create a new top-level definition, using the fresh name and lifted body.
        val defn = SimplifiedAst.Definition.Constant(Ast.Annotations(Nil), name, args, exp, isSynthetic = true, tpe, loc)

        // Update the map that holds newly-generated definitions
        m += (name -> defn)

        // Finally, replace this current Lambda node with a Ref to the newly-generated name.
        SimplifiedAst.Expression.Ref(name, tpe, loc)

      case Expression.Hook(hook, tpe, loc) => e
      case Expression.MkClosureRef(ref, freeVars, tpe, loc) => e

      case SimplifiedAst.Expression.MkClosure(lambda, freeVars, tpe, loc) =>
        // Replace the MkClosure node with a MkClosureRef node, since the Lambda has been replaced by a Ref.
        visit(lambda) match {
          case ref: SimplifiedAst.Expression.Ref =>
            SimplifiedAst.Expression.MkClosureRef(ref, freeVars, tpe, loc)
          case _ => throw InternalCompilerException(s"Unexpected expression: '$lambda'.")
        }

      case Expression.ApplyRef(name, args, tpe, loc) =>
        Expression.ApplyRef(name, args.map(visit), tpe, loc)
      case Expression.ApplyHook(hook, args, tpe, loc) =>
        Expression.ApplyHook(hook, args.map(visit), tpe, loc)
      case Expression.Apply(exp, args, tpe, loc) =>
        Expression.Apply(visit(exp), args.map(visit), tpe, loc)
      case Expression.Unary(op, exp, tpe, loc) =>
        Expression.Unary(op, visit(exp), tpe, loc)
      case Expression.Binary(op, exp1, exp2, tpe, loc) =>
        Expression.Binary(op, visit(exp1), visit(exp2), tpe, loc)
      case Expression.IfThenElse(exp1, exp2, exp3, tpe, loc) =>
        Expression.IfThenElse(visit(exp1), visit(exp2), visit(exp3), tpe, loc)
      case Expression.Let(ident, offset, exp1, exp2, tpe, loc) =>
        Expression.Let(ident, offset, visit(exp1), visit(exp2), tpe, loc)
      case Expression.CheckTag(tag, exp, loc) =>
        Expression.CheckTag(tag, visit(exp), loc)
      case Expression.GetTagValue(tag, exp, tpe, loc) =>
        Expression.GetTagValue(tag, visit(exp), tpe, loc)
      case Expression.Tag(enum, tag, exp, tpe, loc) =>
        Expression.Tag(enum, tag, visit(exp), tpe, loc)
      case Expression.GetTupleIndex(exp, offset, tpe, loc) =>
        Expression.GetTupleIndex(visit(exp), offset, tpe, loc)
      case Expression.Tuple(elms, tpe, loc) =>
        Expression.Tuple(elms.map(visit), tpe, loc)
      case Expression.CheckNil(exp, loc) =>
        Expression.CheckNil(visit(exp), loc)
      case Expression.CheckCons(exp, loc) =>
        Expression.CheckCons(visit(exp), loc)
      case Expression.FSet(elms, tpe, loc) =>
        Expression.FSet(elms.map(visit), tpe, loc)
      case Expression.Existential(params, exp, loc) =>
        Expression.Existential(params, visit(exp), loc)
      case Expression.Universal(params, exp, loc) =>
        Expression.Universal(params, visit(exp), loc)
      case Expression.UserError(tpe, loc) => e
      case Expression.MatchError(tpe, loc) => e
      case Expression.SwitchError(tpe, loc) => e
    }

    visit(exp0)
  }

  /**
    * Lifts expressions out of facts.
    */
  private def lift(fact: SimplifiedAst.Constraint.Fact, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Constraint.Fact = fact.head match {
    case SimplifiedAst.Predicate.Head.Table(sym, terms, tpe, loc) =>
      val lterms = terms.map(t => lift(t, m))
      val lhead = SimplifiedAst.Predicate.Head.Table(sym, lterms, tpe, loc)
      SimplifiedAst.Constraint.Fact(lhead)
  }

  /**
    * Lifts expressions out of rules.
    */
  private def lift(rule: SimplifiedAst.Constraint.Rule, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Constraint.Rule = {
    val head = rule.head match {
      case SimplifiedAst.Predicate.Head.Table(sym, terms, tpe, loc) =>
        val lterms = terms.map(t => lift(t, m))
        SimplifiedAst.Predicate.Head.Table(sym, lterms, tpe, loc)
    }
    SimplifiedAst.Constraint.Rule(head, rule.body.map(b => lift(b, m)))
  }

  /**
    * Lifts expressions out of body predicates.
    */
  private def lift(p: SimplifiedAst.Predicate.Body, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Predicate.Body = p match {
    case SimplifiedAst.Predicate.Body.Table(sym, terms, tpe, loc) =>
      SimplifiedAst.Predicate.Body.Table(sym, terms.map(t => lift(t, m)), tpe, loc)

      // TODO: Need to lift these.
    case SimplifiedAst.Predicate.Body.ApplyFilter(name, terms, tpe, loc) =>
      SimplifiedAst.Predicate.Body.ApplyFilter(name, terms.map(t => lift(t, m)), tpe, loc)

    // TODO: Need to lift these.
    case SimplifiedAst.Predicate.Body.ApplyHookFilter(hook, terms, tpe, loc) =>
      SimplifiedAst.Predicate.Body.ApplyHookFilter(hook, terms.map(t => lift(t, m)), tpe, loc)

    case SimplifiedAst.Predicate.Body.NotEqual(id1, id2, varNum1, varNum2, tpe, loc) =>
      SimplifiedAst.Predicate.Body.NotEqual(id1, id2, varNum1, varNum2, tpe, loc)

    case SimplifiedAst.Predicate.Body.Loop(id, varNum, term, tpe, loc) =>
      SimplifiedAst.Predicate.Body.Loop(id, varNum, lift(term, m), tpe, loc)
  }

  /**
    * Lifts expressions out of head terms.
    */
  private def lift(t: SimplifiedAst.Term.Head, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Term.Head = t match {
    case SimplifiedAst.Term.Head.Var(ident, varNum, tpe, loc) => SimplifiedAst.Term.Head.Var(ident, varNum, tpe, loc)

    case SimplifiedAst.Term.Head.Exp(e, tpe, loc) =>
      // Generate a fresh name for the top-level definition.
      val freshName = genSym.freshDefn(List("head"))

      // Compute the free variables in the hook.
      val free = freeVars(e)

      // Create the  top-level definition with the fresh name and the apply hook as body.
      val formals = free.map {
        case (argName, argType) => SimplifiedAst.FormalArg(argName, argType)
      }
      val defnType = Type.Lambda(formals.map(_.tpe), tpe)
      val defn = SimplifiedAst.Definition.Constant(Ast.Annotations(Nil), freshName, formals, e, isSynthetic = true, defnType, loc)

      // Update the map that holds newly-generated definitions
      m += (freshName -> defn)

      // Return an apply expression calling the generated top-level definition.
      val actuals = free.map {
        case (argName, argType) => SimplifiedAst.Term.Head.Var(argName, -1, argType, SourceLocation.Unknown)
      }
      SimplifiedAst.Term.Head.Apply(freshName, actuals, tpe, loc)

    case SimplifiedAst.Term.Head.Apply(originalName, args, tpe, loc) =>
      // Generate a fresh name for the top-level definition.
      val freshName = genSym.freshDefn(List("head"))

      // Compute the free variables in the hook.
      val free = args.flatMap(a => freeVars(a))

      // Construct the body of the top-level definition.
      val body = SimplifiedAst.Expression.ApplyRef(originalName, args.map(term2exp), tpe, loc)

      // Create the  top-level definition with the fresh name and the apply hook as body.
      val formals = free.map {
        case (argName, argType) => SimplifiedAst.FormalArg(argName, argType)
      }
      val defnType = Type.Lambda(formals.map(_.tpe), tpe)
      val defn = SimplifiedAst.Definition.Constant(Ast.Annotations(Nil), freshName, formals, body, isSynthetic = true, defnType, loc)

      // Update the map that holds newly-generated definitions
      m += (freshName -> defn)

      // Return an apply expression calling the generated top-level definition.
      val actuals = free.map {
        case (argName, argType) => SimplifiedAst.Term.Head.Var(argName, -1, argType, SourceLocation.Unknown)
      }
      SimplifiedAst.Term.Head.Apply(freshName, actuals, tpe, loc)

    case SimplifiedAst.Term.Head.ApplyHook(hook, args, tpe, loc) =>
      // Generate a fresh name for the top-level definition.
      val freshName = genSym.freshDefn(List("head"))

      // Compute the free variables in the hook.
      val free = args.flatMap(a => freeVars(a))

      // Construct the body of the top-level definition.
      val body = SimplifiedAst.Expression.ApplyHook(hook, args.map(term2exp), tpe, loc)

      // Create the  top-level definition with the fresh name and the apply hook as body.
      val formals = free.map {
        case (argName, argType) => SimplifiedAst.FormalArg(argName, argType)
      }
      val defnType = Type.Lambda(formals.map(_.tpe), tpe)
      val defn = SimplifiedAst.Definition.Constant(Ast.Annotations(Nil), freshName, formals, body, isSynthetic = true, defnType, loc)

      // Update the map that holds newly-generated definitions
      m += (freshName -> defn)

      // Return an apply expression calling the generated top-level definition.
      val actuals = free.map {
        case (argName, argType) => SimplifiedAst.Term.Head.Var(argName, -1, argType, SourceLocation.Unknown)
      }
      SimplifiedAst.Term.Head.Apply(freshName, actuals, tpe, loc)
  }

  /**
    * Lifts expressions out of head terms.
    */
  private def lift(t: SimplifiedAst.Term.Body, m: TopLevel)(implicit genSym: GenSym): SimplifiedAst.Term.Body = t match {
    case SimplifiedAst.Term.Body.Wildcard(tpe, loc) => SimplifiedAst.Term.Body.Wildcard(tpe, loc)
    case SimplifiedAst.Term.Body.Var(ident, offset, tpe, loc) => SimplifiedAst.Term.Body.Var(ident, offset, tpe, loc)
    case SimplifiedAst.Term.Body.ApplyRef(name, tpe, loc) => SimplifiedAst.Term.Body.ApplyRef(name, tpe, loc)

    case SimplifiedAst.Term.Body.Exp(e, tpe, loc) =>
      // Generate a fresh name for the top-level definition.
      val freshName = genSym.freshDefn(List("body"))

      // Construct the body of the top-level definition.
      val defnType = Type.Lambda(Nil, tpe)
      val defn = SimplifiedAst.Definition.Constant(Ast.Annotations(Nil), freshName, Nil, e, isSynthetic = true, defnType, loc)

      // Update the map that holds newly-generated definitions
      m += (freshName -> defn)

      SimplifiedAst.Term.Body.ApplyRef(freshName, tpe, loc)
  }

  /**
    * Returns the free variables in the given head term `t`.
    */
  private def freeVars(t: SimplifiedAst.Term.Head): List[(Name.Ident, Type)] = t match {
    case SimplifiedAst.Term.Head.Var(ident, varNum, tpe, loc) => List((ident, tpe))
    case SimplifiedAst.Term.Head.Exp(exp, tpe, loc) => freeVars(exp)
    case SimplifiedAst.Term.Head.Apply(name, args, tpe, loc) => args.flatMap(freeVars)
    case SimplifiedAst.Term.Head.ApplyHook(hook, args, tpe, loc) => args.flatMap(freeVars)
  }

  /**
    * Returns the free variables in the given expression `exp`
    */
  private def freeVars(exp: Expression): List[(Ident, Type)] = exp match {
    case SimplifiedAst.Expression.Unit => Nil
    case SimplifiedAst.Expression.True => Nil
    case SimplifiedAst.Expression.False => Nil
    case SimplifiedAst.Expression.Char(c) => Nil
    case SimplifiedAst.Expression.Float32(f) => Nil
    case SimplifiedAst.Expression.Float64(f) => Nil
    case SimplifiedAst.Expression.Int8(i) => Nil
    case SimplifiedAst.Expression.Int16(i) => Nil
    case SimplifiedAst.Expression.Int32(i) => Nil
    case SimplifiedAst.Expression.Int64(i) => Nil
    case SimplifiedAst.Expression.BigInt(i) => Nil
    case SimplifiedAst.Expression.Str(s) => Nil
    case SimplifiedAst.Expression.LoadBool(e, offset) => freeVars(e)
    case SimplifiedAst.Expression.LoadInt8(e, offset) => freeVars(e)
    case SimplifiedAst.Expression.LoadInt16(e, offset) => freeVars(e)
    case SimplifiedAst.Expression.LoadInt32(e, offset) => freeVars(e)
    case SimplifiedAst.Expression.StoreBool(e1, offset, e2) => freeVars(e1) ::: freeVars(e2)
    case SimplifiedAst.Expression.StoreInt8(e1, offset, e2) => freeVars(e1) ::: freeVars(e2)
    case SimplifiedAst.Expression.StoreInt16(e1, offset, e2) => freeVars(e1) ::: freeVars(e2)
    case SimplifiedAst.Expression.StoreInt32(e1, offset, e2) => freeVars(e1) ::: freeVars(e2)
    case SimplifiedAst.Expression.Var(ident, offset, tpe, loc) => List((ident, tpe))
    case SimplifiedAst.Expression.Ref(name, tpe, loc) => Nil

    case SimplifiedAst.Expression.Tag(enum, tag, e, tpe, loc) => freeVars(e)
    case SimplifiedAst.Expression.Tuple(elms, tpe, loc) => elms.flatMap(freeVars)

    // TODO: Rest
  }

  /**
    * Returns an expression corresponding to the given term.
    */
  private def term2exp(t: SimplifiedAst.Term.Head): SimplifiedAst.Expression = t match {
    case SimplifiedAst.Term.Head.Var(ident, varNum, tpe, loc) => SimplifiedAst.Expression.Var(ident, varNum, tpe, loc)
    case SimplifiedAst.Term.Head.Exp(exp, tpe, loc) => exp
    case SimplifiedAst.Term.Head.Apply(name, args, tpe, loc) =>
      SimplifiedAst.Expression.ApplyRef(name, args.map(term2exp), tpe, loc)
    case SimplifiedAst.Term.Head.ApplyHook(hook, args, tpe, loc) => SimplifiedAst.Expression.ApplyHook(hook, args.map(term2exp), tpe, loc)
  }

}
