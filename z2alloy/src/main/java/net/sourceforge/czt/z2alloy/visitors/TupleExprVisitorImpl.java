package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.ZExprListVisitor;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;

public class TupleExprVisitorImpl extends AbstractVisitor implements
  ZExprListVisitor<List<AlloyExpr>>,
  TupleExprVisitor<List<AlloyExpr>>
{
  
  private PredVisitorAbs pred_;
  
  public TupleExprVisitorImpl(PredVisitorAbs pred) {
    pred_ = pred;
  }

  public List<AlloyExpr> visitZExprList(ZExprList zExprList) {
    List<AlloyExpr> list = new ArrayList<AlloyExpr>();
    for (Expr e : zExprList) {
      list.add(new ExprVisitorImpl(pred_).visit(e));
    }
    return list;
  }
  
  public List<AlloyExpr> visitTupleExpr(TupleExpr tupleExpr) {
    return visitZExprList(tupleExpr.getZExprList());
  }
 
}
