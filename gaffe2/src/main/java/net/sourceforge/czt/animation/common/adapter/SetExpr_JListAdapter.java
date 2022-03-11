
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.DefaultListModel;
import javax.swing.JComponent;
import javax.swing.JList;
import javax.swing.ListModel;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZExprList;

/**
 * @author Linan Zhang
 *
 */
public class SetExpr_JListAdapter extends SetExpr_DefaultAdapter
{
  private JList<String> component;                      // Display the SetExpr as a JList

  /**
   * Constructor
   */
  public SetExpr_JListAdapter()
  {
    super();
    component = new JList<>();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    ListModel<String> model = component.getModel();
    ZExprList exprList = expr.getZExprList();
    exprList.clear();
    String element;
    for (int i = 0; i < model.getSize(); i++) {
      element = model.getElementAt(i);
      exprList.add(GaffeUtil.decodeExpr(element));
    }
    expr.setExprList(exprList);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    ZExprList exprList = expr.getZExprList();
    DefaultListModel<String> model = (DefaultListModel<String>) component.getModel();
    model.clear();
    for (Expr tempExpr : exprList) {
      model.addElement(GaffeUtil.encodeExpr(tempExpr));
    }
    component.setModel(model);
    return component;
  }
}
