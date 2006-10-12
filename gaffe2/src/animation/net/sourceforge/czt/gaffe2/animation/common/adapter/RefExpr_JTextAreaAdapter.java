package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextArea;

import net.sourceforge.czt.z.ast.Expr;

public class RefExpr_JTextAreaAdapter extends RefExpr_DefaultAdapter
{
  private JTextArea component;
  
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
