package net.sourceforge.czt.z2alloy.ast;

public class ExprLet extends AlloyExpr {

  private final ExprVar label;
  private final AlloyExpr var;
  private final AlloyExpr sub;

  public ExprLet(ExprVar label, AlloyExpr var, AlloyExpr sub) {
    super();
    this.label = label;
    this.var = var;
    this.sub = sub;
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public ExprVar label() {
    return label;
  }

  public AlloyExpr var() {
    return var;
  }

  public AlloyExpr sub() {
    return sub;
  }

  public String toString() {
    return "exprlet";
  }
}
