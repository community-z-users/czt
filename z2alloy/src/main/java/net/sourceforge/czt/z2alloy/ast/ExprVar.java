package net.sourceforge.czt.z2alloy.ast;

public class ExprVar extends AlloyExpr {
  private final String label;

  private final AlloyExpr expr;

  public ExprVar(String label, AlloyExpr expr) {
    super();
    this.label = label;
    this.expr = expr;
  }

  public ExprVar(String label) {
    super();
    this.label = label;
    this.expr = null;
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public String label() {
    return label;
  }

  public AlloyExpr expr() {
    return expr;
  }

  public String toString() {
    return label;
  }
}
