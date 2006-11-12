
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.SetExpr;

public class SetExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected SetExpr expr;

  private JTextField component = new JTextField("");

  /**
   * 
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
    expr = (SetExpr) GaffeFactory.decodeExpr(component.getText());
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    component.setText(GaffeFactory.encodeExpr(expr).toString());
    return component;
  }
}
