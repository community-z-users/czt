package net.sourceforge.czt.z2alloy.ast;

import java.util.List;

/**
 * Represents any Alloy expression.
 */
public abstract class AlloyExpr implements Cloneable {

  /**
   * Required by VisitReturn
   */
  public abstract <T> T accept(VisitReturn<T> visitor);

  /** creates a new Expr: this && x */
  public final AlloyExpr and(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.AND, this, x);
  }

  /** creates a new Expr: this || x */
  public final AlloyExpr or(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.OR, this, x);
  }

  /** creates a new Expr: this <=> x */
  public final AlloyExpr iff(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.IFF, this, x);
  }

  /** creates a new Expr: this => y */
  public final AlloyExpr implies(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.IMPLIES, this, x);
  }

  /** creates a new Expr: this . x */
  public final AlloyExpr join(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.JOIN, this, x);
  }

  /** creates a new Expr: this <: x */
  public final AlloyExpr domain(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.DOMAIN, this, x);
  }

  /** creates a new Expr: this :> x */
  public final AlloyExpr range(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.RANGE, this, x);
  }

  /** creates a new Expr: this & x */
  public final AlloyExpr intersect(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.INTERSECT, this, x);
  }

  /** creates a new Expr: this ++ x */
  public final AlloyExpr override(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.PLUSPLUS, this, x);
  }

  /** creates a new Expr: this + x (union or addition) */
  public final AlloyExpr plus(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.PLUS, this, x);
  }

  /** creates a new Expr: this - x (set difference or subtraction) */
  public final AlloyExpr minus(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.MINUS, this, x);
  }

  /** creates a new Expr: this * y */
  public final AlloyExpr mul(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.MUL, this, x);
  }

  /** creates a new Expr: this / y */
  public final AlloyExpr div(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.DIV, this, x);
  }

  /** creates a new Expr: this % y */
  public final AlloyExpr rem(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.REM, this, x);
  }

  /** creates a new Expr: this = x */
  public final AlloyExpr equal(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.EQUALS, this, x);
  }

  /** creates a new Expr: this < x */
  public final AlloyExpr lt(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.LT, this, x);
  }

  /** creates a new Expr: thhis <= x */
  public final AlloyExpr lte(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.LTE, this, x);
  }

  /** creates a new Expr: this > x */
  public final AlloyExpr gt(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.GT, this, x);
  }

  /** creates a new Expr: this >= x */
  public final AlloyExpr gte(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.GTE, this, x);
  }

  /** creates a new Expr: this << x */
  public final AlloyExpr shl(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SHL, this, x);
  }

  /** creates a new Expr: this >>> x */
  public final AlloyExpr shr(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SHR, this, x);
  }

  /** creates a new Expr: this >> x */
  public final AlloyExpr sha(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SHA, this, x);
  }

  /** creates a new Expr: this in x */
  public final AlloyExpr in(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.IN, this, x);
  }

  /** creates a new Expr: this -> x */
  public final AlloyExpr product(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ARROW, this, x);
  }

  /** creates a new Expr: this -> some x */
  public final AlloyExpr any_arrow_some(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ANY_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this -> one x */
  public final AlloyExpr any_arrow_one(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ANY_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this -> lone x */
  public final AlloyExpr any_arrow_lone(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ANY_ARROW_LONE, this, x);
  }

  /** creates a new Expr: this some -> x */
  public final AlloyExpr some_arrow_any(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_ANY, this, x);
  }

  /** creates a new Expr: this some -> some x */
  public final AlloyExpr some_arrow_some(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this some -> one x */
  public final AlloyExpr some_arrow_one(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this some -> lone x */
  public final AlloyExpr some_arrow_lone(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_LONE, this, x);
  }

  /** creates a new Expr: this one -> x */
  public final AlloyExpr one_arrow_any(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_ANY, this, x);
  }

  /** creates a new Expr: this one -> some x */
  public final AlloyExpr one_arrow_some(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this one -> one x */
  public final AlloyExpr one_arrow_one(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this one -> lone x */
  public final AlloyExpr one_arrow_lone(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_LONE, this, x);
  }

  /** creates a new Expr: this lone -> x */
  public final AlloyExpr lone_arrow_any(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_ANY, this, x);
  }

  /** creates a new Expr: this lone -> some x */
  public final AlloyExpr lone_arrow_some(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this lone -> one x */
  public final AlloyExpr lone_arrow_one(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this lone -> lone x */
  public final AlloyExpr lone_arrow_lone(AlloyExpr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_LONE, this, x);
  }

  /** creates a new Expr: seq this */
  public final AlloyExpr seq() {
    return new ExprBinary(ExprBinary.Op.SEQ, Sig.SEQIDX, this);
  }

  /** creates a new Expr: all vars | this */
  public final AlloyExpr forAll(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.ALL, vars, this);
  }

  /** creates a new Expr: no vars | this */
  public final AlloyExpr forNo(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.NO, vars, this);
  }

  /** creates a new Expr: lone vars | this */
  public final AlloyExpr forLone(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.LONE, vars, this);
  }

  /** creates a new Expr: one vars | this */
  public final AlloyExpr forOne(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.ONE, vars, this);
  }

  /** creates a new Expr: some vars | this */
  public final AlloyExpr forSome(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.SOME, vars, this);
  }

  /** creates a new Expr: {vars | this} */
  public final AlloyExpr comprehensionOver(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.COMPREHENSION, vars, this);
  }

  /** creates a new Expr: sum vars | this */
  public final AlloyExpr sumOver(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.SUM, vars, this);
  }

  /** creates a new Expr: some this (used in a decl, eg x : some univ) */
  public final AlloyExpr someOf() {
    return new ExprUnary(ExprUnary.Op.SOMEOF, this);
  }

  /** creates a new Expr: lone this (used in a decl, eg x : lone univ) */
  public final AlloyExpr loneOf() {
    return new ExprUnary(ExprUnary.Op.LONEOF, this);
  }

  /** creates a new Expr: one this (used in a decl, eg x : one univ) */
  public final AlloyExpr oneOf() {
    return new ExprUnary(ExprUnary.Op.ONEOF, this);
  }

  /** creates a new Expr: set this (used in a decl, eg x : set univ) */
  public final AlloyExpr setOf() {
    return new ExprUnary(ExprUnary.Op.SETOF, this);
  }

  /** creates a new Expr: not this */
  public final AlloyExpr not() {
    return new ExprUnary(ExprUnary.Op.NOT, this);
  }

  /** creates a new Expr: no this */
  public final AlloyExpr no() {
    return new ExprUnary(ExprUnary.Op.NO, this);
  }

  /** creates a new Expr: some this */
  public final AlloyExpr some() {
    return new ExprUnary(ExprUnary.Op.SOME, this);
  }

  /** creates a new Expr: lone this */
  public final AlloyExpr lone() {
    return new ExprUnary(ExprUnary.Op.LONE, this);
  }

  /** creates a new Expr: one this */
  public final AlloyExpr one() {
    return new ExprUnary(ExprUnary.Op.ONE, this);
  }

  /** creates a new Expr: ~this */
  public final AlloyExpr transpose() {
    return new ExprUnary(ExprUnary.Op.TRANSPOSE, this);
  }

  /** creates a new Expr: *this */
  public final AlloyExpr reflexiveClosure() {
    return new ExprUnary(ExprUnary.Op.RCLOSURE, this);
  }

  /** creates a new Expr: ^this */
  public final AlloyExpr closure() {
    return new ExprUnary(ExprUnary.Op.CLOSURE, this);
  }

  /** creates a new Expr: #this */
  public final AlloyExpr cardinality() {
    return new ExprUnary(ExprUnary.Op.CARDINALITY, this);
  }

  /** creates a new Expr: int[this] */
  public final AlloyExpr cast2int() {
    return new ExprUnary(ExprUnary.Op.CAST2INT, this);
  }

  /** creates a new Expr: Int[this] */
  public final AlloyExpr cast2sigint() {
    return new ExprUnary(ExprUnary.Op.CAST2SIGINT, this);
  }
}
