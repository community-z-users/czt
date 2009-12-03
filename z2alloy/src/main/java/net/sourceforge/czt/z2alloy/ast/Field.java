package net.sourceforge.czt.z2alloy.ast;

public final class Field extends AlloyExpr {
  private final String label;
  private final AlloyExpr expr;

  public Field(String label, AlloyExpr expr) {
    this.label = label;
    this.expr = expr;
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