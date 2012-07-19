
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class AdapterDefaultImpl implements Adapter
{
  protected Expr expr;                    // The Expression being adapted

  protected JComponent component;         // The UI Component for displaying the expr

  protected static Factory factory;       // The factory for creating expressions.not Gaffe own Factory, but Czt core factory

  protected static ZLive zLive;           // The evaluator reference for gaffe

  /**
   *  Constructor, creating references for all adapters.
   */
  public AdapterDefaultImpl()
  {
    factory = GaffeFactory.getFactory();
    zLive = GaffeFactory.getZLive();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.common.adapter.Adapter#setExpr(net.sourceforge.czt.z.ast.Expr)
   */
  public void setExpr(Expr expr)
  {
    this.expr = expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    return component;
  }

  /* (non-Javadoc)
   * @see java.lang.Object#toString()
   */
  public String toString()
  {
    return this.getClass().getSimpleName();
  }

}
