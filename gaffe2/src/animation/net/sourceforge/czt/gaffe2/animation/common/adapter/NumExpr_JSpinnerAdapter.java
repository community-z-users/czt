package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JSpinner;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class NumExpr_JSpinnerAdapter extends NumExpr_DefaultAdapter
{
  private JSpinner component;
  
  public NumExpr_JSpinnerAdapter()
  {
    super();
    component = new JSpinner();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr(){
    Integer num = Integer.parseInt(component.getValue().toString());
    expr = factory.createNumExpr(num);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent(){
    component.setValue(expr.getValue());
    return component;
  }
  
}
