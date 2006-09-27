
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.DefaultListModel;
import javax.swing.JComponent;
import javax.swing.JList;
import javax.swing.ListModel;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.ZExprList;

/**
 * @author Linan Zhang
 *
 */
public class SetExpr_JListAdapter extends SetExpr_DefaultAdapter
{
  public SetExpr_JListAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#componentToData(javax.swing.JComponent)
   */
  public Expr componentToData(JComponent jc)
  {
    JList component = (JList) jc;
    ListModel model = component.getModel();
    ZExprList exprList = factory.createZExprList();
    String element;
    for (int i = 0; i < model.getSize(); i++) {
      element = (String) model.getElementAt(i);
      exprList.add(factory.createRefExpr(factory.createZRefName(element)));
    }
    return factory.createSetExpr(exprList);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#dataToComponent(javax.swing.JComponent, net.sourceforge.czt.z.ast.Expr)
   */
  public JComponent dataToComponent(JComponent origin, Expr expr)
  {
    JList component = (origin == null)? new JList():(JList) origin;
    SetExpr setExpr = (SetExpr) expr;
    ZExprList exprList = setExpr.getZExprList();
    DefaultListModel model = new DefaultListModel();
    for (Expr tempExpr : exprList) {
      RefExpr value = (RefExpr) tempExpr;
      model.addElement(value.getZRefName().getWord());
    }
    component.setModel(model);
    return component;
  }
}
