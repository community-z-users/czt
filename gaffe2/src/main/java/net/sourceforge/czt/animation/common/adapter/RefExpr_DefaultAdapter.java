
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;

/**
 * @author Linan Zhang
 *
 */
public class RefExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected RefExpr expr;                            // The RefExpr holds a String based Expr

  private JTextField component = new JTextField(""); // Default UI for RefExpr is TextField

  /**
   * Constructor
   */
  public RefExpr_DefaultAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    expr.setName(factory.createZName(component.getText()));
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    component.setText(expr.getZName().getWord());
    return component;
  }
}
