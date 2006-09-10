
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import java.util.ArrayList;

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
public class SetExpr_JListAdapter extends AdapterDefaultImpl
{
  public SetExpr_JListAdapter()
  {
    super();
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
      exprList.add(factory.createRefExpr(factory.createZRefName(element)));
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
      RefExpr value = (RefExpr) tempExpr;
      model.addElement(value.getZRefName().getWord());
    }
    component.setModel(model);
    return component;
  }

  public Object encodeExpr(Expr expr){
    SetExpr setExpr = (SetExpr) expr;
    ZExprList exprList = setExpr.getZExprList();
    ArrayList<String> code = new ArrayList<String>();
    for (Expr tempExpr : exprList) {
      RefExpr value = (RefExpr) tempExpr;
      code.add(value.getZRefName().getWord());
    }
    return code;
  }
  
  @SuppressWarnings("unchecked")
  public Expr decodeExpr(Object code){
    ZExprList exprList = factory.createZExprList();
    ArrayList<String> value = (ArrayList<String>)code;
    for (String temp: value){
      exprList.add(factory.createRefExpr(factory.createZRefName(temp)));
    }
    return factory.createSetExpr(exprList);
  }
}
