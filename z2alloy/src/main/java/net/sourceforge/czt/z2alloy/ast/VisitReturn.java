package net.sourceforge.czt.z2alloy.ast;

/** This abstract class defines what a Return Visitor's interface needs to be. */

public abstract class VisitReturn<T> {

  /** Constructs a VisitReturn object. */
  public VisitReturn() {
  }

  /**
   * This is the start method that begins a traversal over the given expression.
   */
  public final T visitThis(AlloyExpr x) {
    return x.accept(this);
  }

  /** Visits an ExprBinary node. */
  public abstract T visit(ExprBinary x);

  /** Visits an ExprCall node. */
  public abstract T visit(ExprCall x);

  /** Visits an ExprConstant node. */
  public abstract T visit(ExprConstant x);

  /** Visits an ExprITE node. */
  public abstract T visit(ExprITE x);

  /** Visits an ExprLet node. */
  public abstract T visit(ExprLet x);

  /** Visits an ExprQuant node. */
  public abstract T visit(ExprQuant x);

  /** Visits an ExprUnary node. */
  public abstract T visit(ExprUnary x);

  /** Visits an ExprVar node. */
  public abstract T visit(ExprVar x);

  /** Visits a Sig node. */
  public abstract T visit(Sig x);

  /** Visits a Field node. */
  public abstract T visit(Field x);

  /** Visits an Enum node */
  public abstract T visit(Enum x);
}
