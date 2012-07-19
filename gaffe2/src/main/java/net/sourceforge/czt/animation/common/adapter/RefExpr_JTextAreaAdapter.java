
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextArea;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class RefExpr_JTextAreaAdapter extends RefExpr_DefaultAdapter
{
  private JTextArea component;                  // Display RefExpr as TextArea

  /**
   * Constructor
   */
  public RefExpr_JTextAreaAdapter()
  {
    super();
    component = new JTextArea();
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
