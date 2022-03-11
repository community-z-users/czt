
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class BindExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected BindExpr expr;                           // Default expr ref for all BindExpr adapters 

  private JTextField component = new JTextField(""); // Default displayed as TextField

  /**
   * 
   */
  public BindExpr_DefaultAdapter()
  {
    super();
    expr = factory.createBindExpr(factory.createZDeclList());
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    expr = (BindExpr) GaffeUtil.decodeExpr(component.getText());
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    component.setText(GaffeUtil.encodeExpr(expr).toString());
    return component;
  }
}
