
package net.sourceforge.czt.animation.common.adapter;

import java.math.BigInteger;

import javax.swing.JComponent;
import javax.swing.JSpinner;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class NumExpr_JSpinnerAdapter extends NumExpr_DefaultAdapter
{
  private JSpinner component;               // Display Number as JSpinner

  /**
   * Constructor
   */
  public NumExpr_JSpinnerAdapter()
  {
    super();
    component = new JSpinner();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    BigInteger num = new BigInteger(component.getValue().toString());
    expr = factory.createNumExpr(num);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    return component;
  }

}
