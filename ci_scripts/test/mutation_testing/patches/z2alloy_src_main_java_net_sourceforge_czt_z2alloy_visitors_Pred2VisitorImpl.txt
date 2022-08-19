package net.sourceforge.czt.z2alloy.visitors;

import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.IffPred;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.Pred2;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.IffPredVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.OrPredVisitor;
import net.sourceforge.czt.z.visitor.Pred2Visitor;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import edu.mit.csail.sdg.alloy4.Pair;

public class Pred2VisitorImpl extends AbstractVisitor implements
  Pred2Visitor<AlloyExpr>,
  AndPredVisitor<AlloyExpr>,
  IffPredVisitor<AlloyExpr>,
  ImpliesPredVisitor<AlloyExpr>,
  OrPredVisitor<AlloyExpr> {
  
  /**
   * translates an and predicate (ie conjunction) into an alloy and
   * expression.The kind of conjunction used (newline, \and, chain) does not
   * change the result
   * 
   * left and right expressions are recurisvely translated using visit
   * 
   * @return the expression if it successfully translated, or null it something
   *         fails
   */
  public AlloyExpr visitAndPred(AndPred andPred) {
    Pair<AlloyExpr, AlloyExpr> subExprs = subExprs(andPred);
    if (subExprs != null) {
      return subExprs.a.and(subExprs.b);
    }
    return null;
  }

  public AlloyExpr visitIffPred(IffPred iffPred) {
    Pair<AlloyExpr, AlloyExpr> subExprs = subExprs(iffPred);
    if (subExprs != null) {
      return subExprs.a.iff(subExprs.b);
    }
    return null;
  }

  public AlloyExpr visitImpliesPred(ImpliesPred impliesPred) {
    Pair<AlloyExpr, AlloyExpr> subExprs = subExprs(impliesPred);
    if (subExprs != null) {
      return subExprs.a.implies(subExprs.b);
    }
    return null;
  }

  public AlloyExpr visitOrPred(OrPred orPred) {
    Pair<AlloyExpr, AlloyExpr> subExprs = subExprs(orPred);
    if (subExprs != null) {
      return subExprs.a.or(subExprs.b);
    }
    return null;
  }

  private Pair<AlloyExpr, AlloyExpr> subExprs(Pred2 pred2) {
    AlloyExpr left = visit(pred2.getLeftPred());
    AlloyExpr right = visit(pred2.getRightPred());
    if (left == null || right == null) {
      System.err.println("left and right of andpred must not be null");
      return null;
    }
    return new Pair<AlloyExpr, AlloyExpr>(left, right);
  }

  public AlloyExpr visitPred2(Pred2 pred2) {
    if (pred2 != null) {
      return pred2.accept(this);
    }
    return null;
  }
}
