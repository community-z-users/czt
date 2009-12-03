package net.sourceforge.czt.z2alloy.ast;

public class ExprITE extends AlloyExpr {

  private final AlloyExpr cond;

  private final AlloyExpr left;

  private final AlloyExpr right;

  public ExprITE(AlloyExpr cond, AlloyExpr left, AlloyExpr right) {
    this.cond = cond;
    this.left = left;
    this.right = right;
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public AlloyExpr cond() {
    return cond;
  }

  public AlloyExpr left() {
    return left;
  }

  public AlloyExpr right() {
    return right;
  }

  public String toString() {
    return "exprite";
  }

}
