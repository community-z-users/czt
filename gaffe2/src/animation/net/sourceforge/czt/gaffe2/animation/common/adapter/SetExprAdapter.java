
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.DefaultListModel;
import javax.swing.JComponent;
import javax.swing.JList;
import javax.swing.ListModel;

import net.sourceforge.czt.animation.eval.GivenValue;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class SetExprAdapter implements Adapter
{
  private Factory factory;

  public SetExprAdapter()
  {
    factory = GaffeFactory.getFactory();
  }

  //Retrieve data from input components
  public Expr componentToData(JComponent jc)
  {
    JList component = (JList) jc;
    ListModel model = component.getModel();
    ZExprList exprList = factory.createZExprList();
    String element;
    for (int i = 0; i < model.getSize(); i++) {
      element = (String) model.getElementAt(i);
      exprList.add(new GivenValue(element));
    }
    return factory.createSetExpr(exprList);
  }

  // Update components with changed data
  public JComponent dataToComponent(JComponent origin, Expr expr)
  {
    if (origin == null) {
      origin = new JList();
    }
    JList component = (JList) origin;
    SetExpr setExpr = (SetExpr) expr;
    ZExprList exprList = setExpr.getZExprList();
    DefaultListModel model = new DefaultListModel();
    for (Expr tempExpr : exprList) {
      GivenValue value = (GivenValue) tempExpr;
      model.addElement(value.getValue());
    }
    component.setModel(model);
    return component;
  }

}
