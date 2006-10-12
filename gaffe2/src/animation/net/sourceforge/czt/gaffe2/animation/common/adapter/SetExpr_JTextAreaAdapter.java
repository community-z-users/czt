package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextArea;

import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZExprList;

public class SetExpr_JTextAreaAdapter extends SetExpr_DefaultAdapter
{
  private JTextArea component;
  
  public SetExpr_JTextAreaAdapter()
  {
    super();
    component = new JTextArea("");
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    String text = component.getText();
    String r[] = text.split(System.getProperty("line.separator"));
    int i = 0;
    String temp;
    ZExprList result = expr.getZExprList();
    result.clear();
    for (i = 0; i < r.length; i++) {
      temp = r[i];
      Expr value = (temp!=null)? GaffeFactory.decodeExpr(temp):null;
      result.add(value);
    }
    expr.setExprList(result);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    ZExprList exprList = expr.getZExprList();
    component.setText("");
    String temp = "";
    int i = 0;
    for (Expr exprElem : exprList) {
      temp += GaffeFactory.encodeExpr(exprElem);
      temp += System.getProperty("line.separator");
      component.append(temp);
      i++;
    }
    return component;
  }
  
}
