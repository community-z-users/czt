
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;

public class BindExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected BindExpr expr;

  private JTextField component = new JTextField("");

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
    expr = (BindExpr) GaffeFactory.decodeExpr(component.getText());
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
