package net.sourceforge.czt.z2alloy.ast;

public class Fact {

  private final AlloyExpr expr;
  private final String label;

  public Fact(AlloyExpr expr, String label) {
    this.expr = expr;
    this.label = label;
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
