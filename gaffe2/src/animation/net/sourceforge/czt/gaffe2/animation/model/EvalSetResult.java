/**
 * 
 */

package net.sourceforge.czt.gaffe2.animation.model;

import java.util.HashMap;
import java.util.ListIterator;

import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;

/**
 * @author Linan Zhang
 *
 */
public class EvalSetResult implements EvalResult
{
  private EvalSet evalSet;

  private ListIterator<Expr> iterator;

  /**
   * @param evalSet
   */
  public EvalSetResult(EvalSet evalSet)
  {
    this.evalSet = evalSet;
    iterator = evalSet.listIterator();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#isFinite()
   */
  public boolean isFinite()
  {
    // How to know whether the evalResult is finite or not
    return (evalSet.estSize() != Double.MAX_VALUE);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#hasNext()
   */
  public boolean hasNext()
  {
    return this.iterator.hasNext();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#hasPrevious()
   */
  public boolean hasPrevious()
  {
    return this.iterator.hasPrevious();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#first()
   */
  public HashMap<String, Expr> first()
  {
    BindExpr bindExpr = null;
    while (this.iterator.hasPrevious()) {
      bindExpr = (BindExpr) iterator.previous();
    }
    return bindExprToHashMap(bindExpr);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#last()
   */
  public HashMap<String, Expr> last()
  {
    BindExpr bindExpr = null;
    while (this.iterator.hasNext()) {
      bindExpr = (BindExpr) iterator.next();
    }
    return bindExprToHashMap(bindExpr);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#next()
   */
  public HashMap<String, Expr> next()
  {
    if (hasNext()) {
      BindExpr bindExpr = (BindExpr) this.iterator.next();
      return bindExprToHashMap(bindExpr);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#previous()
   */
  public HashMap<String, Expr> previous()
  {
    if (hasPrevious()) {
      BindExpr bindExpr = (BindExpr) this.iterator.previous();
      return bindExprToHashMap(bindExpr);
    }
    else {
      return null;
    }
  }

  

  /**
   * @param expr
   * @return
   */
  private HashMap<String, Expr> bindExprToHashMap(BindExpr expr)
  {
    ZDeclList declList = expr.getZDeclList();
    HashMap<String, Expr> result = new HashMap<String, Expr>();
    for (Decl decl : declList) {
      ConstDecl constDecl = (ConstDecl) decl;
      DeclName declName = constDecl.getDeclName();
      Expr declExpr = constDecl.getExpr();
      result.put(declName.toString(), declExpr);
    }
    return result;
  }
}
