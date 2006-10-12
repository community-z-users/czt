package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;

public class NumExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected NumExpr expr;
  private JTextField component = new JTextField("");
  
  public NumExpr_DefaultAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr(){
    int num = Integer.parseInt(component.getText());
    expr = factory.createNumExpr(num);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#setExpr(net.sourceforge.czt.z.ast.Expr)
   */
  public void setExpr(Expr expr)
  {
    this.expr = (NumExpr)expr;
  }
  
  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent(){
    component.setText(expr.getValue().toString());
    return component;
  }
}
