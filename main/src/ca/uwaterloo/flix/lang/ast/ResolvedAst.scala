package ca.uwaterloo.flix.lang.ast

trait ResolvedAst

object ResolvedAst {

  // TODO Replace QName by RName.
  case class RName() extends ResolvedAst

  sealed trait Declaration extends ResolvedAst

  object Declaration {

    case class Fact(head: ResolvedAst.Predicate) extends Declaration


  }

  sealed trait Definition extends ResolvedAst.Declaration

  object Definition {

    case class Relation() extends ResolvedAst.Definition

  }

  sealed trait Literal

  object Literal {

    case object Unit extends ResolvedAst.Literal

    case class Bool(literal: scala.Boolean) extends ResolvedAst.Literal

    case class Int(literal: scala.Int) extends ResolvedAst.Literal

    case class Str(literal: java.lang.String) extends ResolvedAst.Literal

    case class Tag(name: ResolvedAst.RName, ident: ParsedAst.Ident, literal: ResolvedAst.Literal, defn: WeededAst.Definition.Enum) extends ResolvedAst.Literal

    case class Tuple(elms: Seq[ResolvedAst.Literal]) extends ResolvedAst.Literal

  }

  sealed trait Expression extends Definition

  object Expression {

    case class Var(ident: ParsedAst.Ident) extends ResolvedAst.Expression

    case class Ref(name: ResolvedAst.RName, defn: WeededAst.Definition) extends ResolvedAst.Expression

    case class Lit(literal: ResolvedAst.Literal) extends ResolvedAst.Expression

    case class Lambda(formals: Seq[(ParsedAst.Ident, ResolvedAst.Type)], returnType: ResolvedAst.Type, body: ResolvedAst.Expression) extends ResolvedAst.Expression

    case class Apply(lambda: ResolvedAst.Expression, args: Seq[ResolvedAst.Expression]) extends ResolvedAst.Expression

    case class Unary(op: UnaryOperator, e: ResolvedAst.Expression) extends ResolvedAst.Expression

    case class Binary(e1: ResolvedAst.Expression, op: BinaryOperator, e2: ResolvedAst.Expression) extends ResolvedAst.Expression

    case class IfThenElse(e1: ResolvedAst.Expression, e2: ResolvedAst.Expression, e3: ResolvedAst.Expression) extends ResolvedAst.Expression

    case class Let(ident: ParsedAst.Ident, value: ResolvedAst.Expression, body: ResolvedAst.Expression) extends ResolvedAst.Expression

    case class Match(e: ResolvedAst.Expression, rules: Seq[(ResolvedAst.Pattern, ResolvedAst.Expression)]) extends ResolvedAst.Expression

    case class Tag(name: ResolvedAst.RName, ident: ParsedAst.Ident, e: ResolvedAst.Expression, defn: WeededAst.Definition.Enum) extends ResolvedAst.Expression

    case class Tuple(elms: Seq[ResolvedAst.Expression]) extends ResolvedAst.Expression

    case class Ascribe(e: ResolvedAst.Expression) extends ResolvedAst.Expression

    case class Error(location: SourceLocation) extends ResolvedAst.Expression

  }

  sealed trait Pattern extends ResolvedAst

  object Pattern {

    case class Wildcard(location: SourceLocation) extends ResolvedAst.Pattern

    case class Var(ident: ParsedAst.Ident) extends ResolvedAst.Pattern

    case class Lit(literal: ResolvedAst.Literal) extends ResolvedAst.Pattern

    case class Tag(name: ResolvedAst.RName, ident: ParsedAst.Ident, p: ResolvedAst.Pattern) extends ResolvedAst.Pattern

    case class Tuple(elms: Seq[ResolvedAst.Pattern]) extends ResolvedAst.Pattern

  }

  sealed trait Predicate

  object Predicate {

    case class Relational(/* todo: what */) extends ResolvedAst.Predicate

    case class Functional(/*  todo: what */) extends ResolvedAst.Predicate

  }

  sealed trait Type extends ResolvedAst

  object Type {

  }

}