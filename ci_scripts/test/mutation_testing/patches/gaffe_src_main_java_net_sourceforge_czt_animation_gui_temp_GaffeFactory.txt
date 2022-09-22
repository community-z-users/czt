
package net.sourceforge.czt.animation.gui.temp;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.GivenValue;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan
 * 
 */

public class GaffeFactory
{
  /* Initialise the ZLive only once */
  private static ZLive zLive_ = new ZLive();

  /** No one can create instances of this class. */
  private GaffeFactory()
  {
  }

  /**
   * return the unique reference of Factory in ZLive
   * @return a static reference to factory
   */
  public static Factory getFactory()
  {
    return zLive_.getFactory();
  }

  /**
   * Return the unique reference to ZLive
   * @return a static reference to ZLive
   */
  public static ZLive getZLive()
  {
    return zLive_;
  }

  /**
   * @param e The expr being transformed
   * @return The ZValue representing the expr
   * @throws UnexpectedTypeException
   */
  public static ZValue zValue(Expr e) throws UnexpectedTypeException
  {
    if (e instanceof NumExpr) {
      return new ZNumber((NumExpr) e);
    }
    else if (e instanceof GivenValue) {
      return new ZGiven((GivenValue) e);
    }
    else if (e instanceof TupleExpr) {
      return new ZTuple((TupleExpr) e);
    }
    else if (e instanceof EvalSet) {
      return new ZSet((EvalSet) e);
    }
    else if (e instanceof BindExpr) {
      return new ZBinding((BindExpr) e);
    }
    else {
      throw new UnexpectedTypeException(
          "Unexpected Expr type, couldn't covert Expr to ZValue " + e);
    }
  }
}
