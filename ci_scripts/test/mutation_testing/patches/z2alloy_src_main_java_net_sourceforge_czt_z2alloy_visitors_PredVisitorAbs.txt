package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;
import net.sourceforge.czt.z2alloy.ast.ExprQuant;
import net.sourceforge.czt.z2alloy.ast.ExprVar;

public class PredVisitorAbs extends AbstractVisitor implements PredVisitor<AlloyExpr> {
  
  private List<ExprVar> thetaVars = new ArrayList<ExprVar>();
  private AlloyExpr thetaPred = ExprConstant.TRUE;
  
  public AlloyExpr visitPred(Pred pred) {
    if (pred != null) {
      AlloyExpr alloyPred = pred.accept(this);
      if (!thetaVars.isEmpty()) {
        alloyPred = new ExprQuant(ExprQuant.Op.SOME, thetaVars, thetaPred.and(alloyPred));
      }
      return alloyPred;
    }
    return null;
  }

  protected AlloyExpr visit(Expr expr) {
    return new ExprVisitorImpl(this).visitExpr(expr);
  }
  
  public void theta(ExprVar var, AlloyExpr pred) {
    for (ExprVar exprVar : thetaVars) {
      if (exprVar.label().equals(var.label())) return;
    }
    thetaVars.add(var);
    thetaPred = (thetaPred == ExprConstant.TRUE ? pred : pred.and(thetaPred));
  }

}