
package net.sourceforge.czt.animation.model;

import java.util.HashMap;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public interface EvalResult
{

  /**
   * @return whether this evaluation result is finite or not 
   */
  public boolean isFinite();

  /**
   * @return whether it has a next result base on current iterator
   */
  public boolean hasNext();

  /**
   * @return whether it has a previous result base on current iterator
   */
  public boolean hasPrevious();

  /**
   * @return the first result
   */
  public HashMap<String, Expr> first();

  /**
   * @return the last result
   */
  public HashMap<String, Expr> last();

  /**
   * @return next result
   */
  public HashMap<String, Expr> next();

  /**
   * @return previous result
   */
  public HashMap<String, Expr> previous();
}
