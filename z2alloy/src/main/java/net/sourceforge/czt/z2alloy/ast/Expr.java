package net.sourceforge.czt.z2alloy.ast;

import java.util.List;

/**
 * Represents any Alloy expression.
 */
public abstract class Expr implements Cloneable {

  /**
   * Required by VisitReturn
   */
  public abstract <T> T accept(VisitReturn<T> visitor);

  /** creates a new Expr: this && x */
  public final Expr and(Expr x) {
    return new ExprBinary(ExprBinary.Op.AND, this, x);
  }

  /** creates a new Expr: this || x */
  public final Expr or(Expr x) {
    return new ExprBinary(ExprBinary.Op.OR, this, x);
  }

  /** creates a new Expr: this <=> x */
  public final Expr iff(Expr x) {
    return new ExprBinary(ExprBinary.Op.IFF, this, x);
  }

  /** creates a new Expr: this => y */
  public final Expr implies(Expr x) {
    return new ExprBinary(ExprBinary.Op.IMPLIES, this, x);
  }

  /** creates a new Expr: this . x */
  public final Expr join(Expr x) {
    return new ExprBinary(ExprBinary.Op.JOIN, this, x);
  }

  /** creates a new Expr: this <: x */
  public final Expr domain(Expr x) {
    return new ExprBinary(ExprBinary.Op.DOMAIN, this, x);
  }

  /** creates a new Expr: this :> x */
  public final Expr range(Expr x) {
    return new ExprBinary(ExprBinary.Op.RANGE, this, x);
  }

  /** creates a new Expr: this & x */
  public final Expr intersect(Expr x) {
    return new ExprBinary(ExprBinary.Op.INTERSECT, this, x);
  }

  /** creates a new Expr: this ++ x */
  public final Expr override(Expr x) {
    return new ExprBinary(ExprBinary.Op.PLUSPLUS, this, x);
  }

  /** creates a new Expr: this + x (union or addition) */
  public final Expr plus(Expr x) {
    return new ExprBinary(ExprBinary.Op.PLUS, this, x);
  }

  /** creates a new Expr: this - x (set difference or subtraction) */
  public final Expr minus(Expr x) {
    return new ExprBinary(ExprBinary.Op.MINUS, this, x);
  }

  /** creates a new Expr: this * y */
  public final Expr mul(Expr x) {
    return new ExprBinary(ExprBinary.Op.MUL, this, x);
  }

  /** creates a new Expr: this / y */
  public final Expr div(Expr x) {
    return new ExprBinary(ExprBinary.Op.DIV, this, x);
  }

  /** creates a new Expr: this % y */
  public final Expr rem(Expr x) {
    return new ExprBinary(ExprBinary.Op.REM, this, x);
  }

  /** creates a new Expr: this = x */
  public final Expr equal(Expr x) {
    return new ExprBinary(ExprBinary.Op.EQUALS, this, x);
  }

  /** creates a new Expr: this < x */
  public final Expr lt(Expr x) {
    return new ExprBinary(ExprBinary.Op.LT, this, x);
  }

  /** creates a new Expr: thhis <= x */
  public final Expr lte(Expr x) {
    return new ExprBinary(ExprBinary.Op.LTE, this, x);
  }

  /** creates a new Expr: this > x */
  public final Expr gt(Expr x) {
    return new ExprBinary(ExprBinary.Op.GT, this, x);
  }

  /** creates a new Expr: this >= x */
  public final Expr gte(Expr x) {
    return new ExprBinary(ExprBinary.Op.GTE, this, x);
  }

  /** creates a new Expr: this << x */
  public final Expr shl(Expr x) {
    return new ExprBinary(ExprBinary.Op.SHL, this, x);
  }

  /** creates a new Expr: this >>> x */
  public final Expr shr(Expr x) {
    return new ExprBinary(ExprBinary.Op.SHR, this, x);
  }

  /** creates a new Expr: this >> x */
  public final Expr sha(Expr x) {
    return new ExprBinary(ExprBinary.Op.SHA, this, x);
  }

  /** creates a new Expr: this in x */
  public final Expr in(Expr x) {
    return new ExprBinary(ExprBinary.Op.IN, this, x);
  }

  /** creates a new Expr: this -> x */
  public final Expr product(Expr x) {
    return new ExprBinary(ExprBinary.Op.ARROW, this, x);
  }

  /** creates a new Expr: this -> some x */
  public final Expr any_arrow_some(Expr x) {
    return new ExprBinary(ExprBinary.Op.ANY_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this -> one x */
  public final Expr any_arrow_one(Expr x) {
    return new ExprBinary(ExprBinary.Op.ANY_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this -> lone x */
  public final Expr any_arrow_lone(Expr x) {
    return new ExprBinary(ExprBinary.Op.ANY_ARROW_LONE, this, x);
  }

  /** creates a new Expr: this some -> x */
  public final Expr some_arrow_any(Expr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_ANY, this, x);
  }

  /** creates a new Expr: this some -> some x */
  public final Expr some_arrow_some(Expr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this some -> one x */
  public final Expr some_arrow_one(Expr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this some -> lone x */
  public final Expr some_arrow_lone(Expr x) {
    return new ExprBinary(ExprBinary.Op.SOME_ARROW_LONE, this, x);
  }

  /** creates a new Expr: this one -> x */
  public final Expr one_arrow_any(Expr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_ANY, this, x);
  }

  /** creates a new Expr: this one -> some x */
  public final Expr one_arrow_some(Expr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this one -> one x */
  public final Expr one_arrow_one(Expr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this one -> lone x */
  public final Expr one_arrow_lone(Expr x) {
    return new ExprBinary(ExprBinary.Op.ONE_ARROW_LONE, this, x);
  }

  /** creates a new Expr: this lone -> x */
  public final Expr lone_arrow_any(Expr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_ANY, this, x);
  }

  /** creates a new Expr: this lone -> some x */
  public final Expr lone_arrow_some(Expr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_SOME, this, x);
  }

  /** creates a new Expr: this lone -> one x */
  public final Expr lone_arrow_one(Expr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_ONE, this, x);
  }

  /** creates a new Expr: this lone -> lone x */
  public final Expr lone_arrow_lone(Expr x) {
    return new ExprBinary(ExprBinary.Op.LONE_ARROW_LONE, this, x);
  }

  /** creates a new Expr: seq this */
  public final Expr seq() {
    return new ExprBinary(ExprBinary.Op.SEQ, Sig.SEQIDX, this);
  }

  /** creates a new Expr: all vars | this */
  public final Expr forAll(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.ALL, vars, this);
  }

  /** creates a new Expr: no vars | this */
  public final Expr forNo(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.NO, vars, this);
  }

  /** creates a new Expr: lone vars | this */
  public final Expr forLone(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.LONE, vars, this);
  }

  /** creates a new Expr: one vars | this */
  public final Expr forOne(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.ONE, vars, this);
  }

  /** creates a new Expr: some vars | this */
  public final Expr forSome(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.SOME, vars, this);
  }

  /** creates a new Expr: {vars | this} */
  public final Expr comprehensionOver(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.COMPREHENSION, vars, this);
  }

  /** creates a new Expr: sum vars | this */
  public final Expr sumOver(List<ExprVar> vars) {
    return new ExprQuant(ExprQuant.Op.SUM, vars, this);
  }

  /** creates a new Expr: some this (used in a decl, eg x : some univ) */
  public final Expr someOf() {
    return new ExprUnary(ExprUnary.Op.SOMEOF, this);
  }

  /** creates a new Expr: lone this (used in a decl, eg x : lone univ) */
  public final Expr loneOf() {
    return new ExprUnary(ExprUnary.Op.LONEOF, this);
  }

  /** creates a new Expr: one this (used in a decl, eg x : one univ) */
  public final Expr oneOf() {
    return new ExprUnary(ExprUnary.Op.ONEOF, this);
  }

  /** creates a new Expr: set this (used in a decl, eg x : set univ) */
  public final Expr setOf() {
    return new ExprUnary(ExprUnary.Op.SETOF, this);
  }

  /** creates a new Expr: not this */
  public final Expr not() {
    return new ExprUnary(ExprUnary.Op.NOT, this);
  }

  /** creates a new Expr: no this */
  public final Expr no() {
    return new ExprUnary(ExprUnary.Op.NO, this);
  }

  /** creates a new Expr: some this */
  public final Expr some() {
    return new ExprUnary(ExprUnary.Op.SOME, this);
  }

  /** creates a new Expr: lone this */
  public final Expr lone() {
    return new ExprUnary(ExprUnary.Op.LONE, this);
  }

  /** creates a new Expr: one this */
  public final Expr one() {
    return new ExprUnary(ExprUnary.Op.ONE, this);
  }

  /** creates a new Expr: ~this */
  public final Expr transpose() {
    return new ExprUnary(ExprUnary.Op.TRANSPOSE, this);
  }

  /** creates a new Expr: *this */
  public final Expr reflexiveClosure() {
    return new ExprUnary(ExprUnary.Op.RCLOSURE, this);
  }

  /** creates a new Expr: ^this */
  public final Expr closure() {
    return new ExprUnary(ExprUnary.Op.CLOSURE, this);
  }

  /** creates a new Expr: #this */
  public final Expr cardinality() {
    return new ExprUnary(ExprUnary.Op.CARDINALITY, this);
  }

  /** creates a new Expr: int[this] */
  public final Expr cast2int() {
    return new ExprUnary(ExprUnary.Op.CAST2INT, this);
  }

  /** creates a new Expr: Int[this] */
  public final Expr cast2sigint() {
    return new ExprUnary(ExprUnary.Op.CAST2SIGINT, this);
  }
}
