package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;


public class RefExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected RefExpr expr;
  private JTextField component = new JTextField("");
  
  public RefExpr_DefaultAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    expr.setRefName(factory.createZRefName(component.getText()));
    return expr;
  }
  
  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    component.setText(expr.getZRefName().getWord());
    return component;
  }
}
