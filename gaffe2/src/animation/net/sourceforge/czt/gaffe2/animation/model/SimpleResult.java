
package net.sourceforge.czt.gaffe2.animation.model;

import java.util.HashMap;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class SimpleResult implements EvalResult
{
  private List<HashMap<String, Expr>> solutionList;

  private ListIterator<HashMap<String, Expr>> iterator;

  /**
   * @param solutionList
   */
  public SimpleResult(List<HashMap<String, Expr>> solutionList)
  {
    this.solutionList = solutionList;
    iterator = solutionList.listIterator();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#isFinite()
   */
  public boolean isFinite()
  {
    return true;
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
    while (iterator.hasPrevious()) {
      iterator.previous();
    }
    return solutionList.get(0);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#last()
   */
  public HashMap<String, Expr> last()
  {
    while (iterator.hasNext()) {
      iterator.next();
    }
    return solutionList.get(solutionList.size() - 1);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#next()
   */
  public HashMap<String, Expr> next()
  {
    if (hasNext()) {
      return iterator.next();
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
      return iterator.previous();
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.model.EvalResult#size()
   */
  public int size()
  {
    return solutionList.size();
  }
}
