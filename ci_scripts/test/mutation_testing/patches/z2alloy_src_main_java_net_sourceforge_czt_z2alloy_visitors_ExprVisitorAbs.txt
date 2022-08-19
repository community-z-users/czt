package net.sourceforge.czt.z2alloy.visitors;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprVar;

public abstract class ExprVisitorAbs extends AbstractVisitor implements ExprVisitor<AlloyExpr> {
  
  private PredVisitorAbs pred_;
  
  public ExprVisitorAbs(PredVisitorAbs pred) {
    pred_ = pred;
  }

  public AlloyExpr visitExpr(Expr expr) {
    if (expr != null) {
      return expr.accept(new ExprVisitorImpl(pred_));
    }
    return null;
  }
  
  protected AlloyExpr visit(Expr expr) {
    return visitExpr(expr);
  }
  
  protected PredVisitorAbs pred() {
    return pred_;
  }
  
  protected void theta(ExprVar vars, AlloyExpr pred) {
    if (pred_ != null) {
      pred_.theta(vars, pred);
    }
  }

}
