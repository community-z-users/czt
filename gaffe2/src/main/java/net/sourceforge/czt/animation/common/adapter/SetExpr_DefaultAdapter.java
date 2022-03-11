
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.SetExpr;

/**
 * @author Linan Zhang
 *
 */
public class SetExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected SetExpr expr;                            // The SetExpr ref hold by all SetExpr Adapters

  private JTextField component = new JTextField(""); // Display SefExpr as a TextField

  /**
   * Constructor
   */
  public SetExpr_DefaultAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    expr = (SetExpr) GaffeUtil.decodeExpr(component.getText());
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
