package net.sourceforge.czt.z2alloy.visitors;

import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.Pred2;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NegPredVisitor;
import net.sourceforge.czt.z.visitor.Pred2Visitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;

public class PredVisitorImpl extends PredVisitorAbs implements
MemPredVisitor<AlloyExpr>,
NegPredVisitor<AlloyExpr>,
Pred2Visitor<AlloyExpr>,
QntPredVisitor<AlloyExpr>,
TruePredVisitor<AlloyExpr>
{
  
  /**
   * kinds of MemPred currently translated:
   * 
   * <pre>
   * equality                   left = right
   * notin                      ! left in right
   * subseteq                   left in right
   * subset                     left in right and (not left = right)
   * less                       left &lt; right
   * leq                        left &lt;= right
   * greater                    left &gt; right
   * geq                        left &gt;= right
   * neq                        ! left = right
   * </pre>
   * 
   * otherwise assumes it is membership => left in right
   */
  public AlloyExpr visitMemPred(MemPred memPred) {
    if (memPred.getRightExpr() instanceof SetExpr
        && ((SetExpr) memPred.getRightExpr()).getZExprList().size() == 1) {
      // equality
      AlloyExpr left = new ExprVisitorImpl(this).visitExpr(memPred.getLeftExpr());
      AlloyExpr right = visit(memPred.getRightExpr());
      if (left == null || right == null) {
        System.err.println("Left and right of memPred must be non null");
        throw new RuntimeException();
      }
      return left.equal(right);
    }
    if (memPred.getLeftExpr() instanceof TupleExpr
        && memPred.getRightExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) memPred.getRightExpr();
      ZExprList exprs = ((TupleExpr) memPred.getLeftExpr()).getZExprList();
      AlloyExpr left = visit(exprs.get(0));
      AlloyExpr right = visit(exprs.get(1));
      if (left == null || right == null) {
        System.err.println("Left and right of refExpr must be non null");
        throw new RuntimeException();
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.NOTMEM)) {
        return left.in(right).not();
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.SUBSETEQ)) {
        return left.in(right);
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.SUBSET)) {
        return left.in(right).and(left.equal(right).not());
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.LESS)) {
        return left.lt(right);
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.LEQ)) {
        return left.lte(right);
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.GREATER)) {
        return left.gt(right);
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.GEQ)) {
        return left.gte(right);
      }
      if (Z2Alloy.isInfixOperator(refExpr.getZName(), ZString.NEQ)) {
        return left.equal(right).not();
      }
    }
    AlloyExpr left = visit(memPred.getLeftExpr());
    AlloyExpr right = visit(memPred.getRightExpr());
    if (left == null || right == null) {
      System.err.println("Left and right Expr of MemPred must not be null");
      throw new RuntimeException();
    }
    return left.in(right);
  }

  public AlloyExpr visitNegPred(NegPred negPred) {
    return visitPred(negPred.getPred()).not();
  }
  
  public AlloyExpr visitPred2(Pred2 pred2) {
    return new Pred2VisitorImpl().visitPred2(pred2);
  }
  
  public AlloyExpr visitQntPred(QntPred qntPred) {
    return new QntPredVisitorImpl().visitQntPred(qntPred);
  }
  
  public AlloyExpr visitTruePred(TruePred arg0) {
    return ExprConstant.TRUE;
  }
  
}
