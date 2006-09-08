
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;

import net.sourceforge.czt.animation.eval.GivenValue;
import net.sourceforge.czt.animation.gui.temp.GaffeFactory;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class BindExprAdapter implements Adapter
{
  private Factory factory;

  public BindExprAdapter()
  {
    factory = GaffeFactory.getFactory();
  }

  //Retrieve data from input components
  public Expr componentToData(JComponent jc)
  {
    JTable component = (JTable) jc;
    TableModel tm = component.getModel();
    int i = 0;
    String temp;
    ZDeclList result = factory.createZDeclList();
    for (i = 0; i < tm.getRowCount(); i++) {
      temp = (String) tm.getValueAt(i, 0);
      ZDeclName name = factory.createZDeclName(temp);
      temp = (String) tm.getValueAt(i, 1);
      GivenValue value = new GivenValue(temp);
      result.add((Decl) factory.createConstDecl(name, value));
    }
    return factory.createBindExpr(result);
  }

  // Update components with changed data
  public JComponent dataToComponent(JComponent origin, Expr expr)
  {
    BindExpr bindExpr = (BindExpr) expr;
    ZDeclList declList = bindExpr.getZDeclList();
    if (origin == null) {
      DefaultTableModel dataModel = new DefaultTableModel();
      dataModel.addColumn("unknown");
      dataModel.addColumn("unknown");
      return new JTable(dataModel);
    }
    else {
      Object[][] dataModel = new Object[declList.size()][2];
      int i = 0;
      for (Decl decl : declList) {
        ConstDecl tempDecl = (ConstDecl) decl;
        dataModel[i][0] = tempDecl.getZDeclName().toString();
        dataModel[i][1] = ((GivenValue) tempDecl.getExpr()).getValue();
        i++;
      }
      JTable component = (JTable) origin;
      TableModel tm = component.getModel();
      String columnName1 = tm.getColumnName(0);
      String columnName2 = tm.getColumnName(1);
      component.setModel(new DefaultTableModel(dataModel, new String[]{
          columnName1, columnName2}));
      return component;
    }
  }
}
