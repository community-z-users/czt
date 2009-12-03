package net.sourceforge.czt.z2alloy.visitors;

import net.sourceforge.czt.base.ast.Term;
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
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.Expr;
import edu.mit.csail.sdg.alloy4.Pair;

public class Pred2VisitorImpl implements Pred2Visitor<Expr>,
    AndPredVisitor<Expr>, IffPredVisitor<Expr>, ImpliesPredVisitor<Expr>,
    OrPredVisitor<Expr> {

  public Expr visit(Term t) {
    if (t != null) {
      Expr e = t.accept(this);
      return e;
    }
    return null;
  }

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
  public Expr visitAndPred(AndPred andPred) {
    Pair<Expr, Expr> subExprs = subExprs(andPred);
    if (subExprs != null) {
      return subExprs.a.and(subExprs.b);
    }
    return null;
  }

  public Expr visitIffPred(IffPred iffPred) {
    Pair<Expr, Expr> subExprs = subExprs(iffPred);
    if (subExprs != null) {
      return subExprs.a.iff(subExprs.b);
    }
    return null;
  }

  public Expr visitImpliesPred(ImpliesPred impliesPred) {
    Pair<Expr, Expr> subExprs = subExprs(impliesPred);
    if (subExprs != null) {
      return subExprs.a.implies(subExprs.b);
    }
    return null;
  }

  public Expr visitOrPred(OrPred orPred) {
    Pair<Expr, Expr> subExprs = subExprs(orPred);
    if (subExprs != null) {
      return subExprs.a.or(subExprs.b);
    }
    return null;
  }

  private Pair<Expr, Expr> subExprs(Pred2 pred2) {
    Expr left = Z2Alloy.getInstance().visit(pred2.getLeftPred());
    Expr right = Z2Alloy.getInstance().visit(pred2.getRightPred());
    if (left == null || right == null) {
      System.err.println("left and right of andpred must not be null");
      return null;
    }
    return new Pair<Expr, Expr>(left, right);
  }

  public Expr visitPred2(Pred2 pred2) {
    System.err.println(pred2 + " is not implemented yet");
    return null;
  }
}
