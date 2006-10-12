
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;

import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;

/**
 * @author Linan Zhang
 *
 */
public class BindExpr_JTableAdapter extends BindExpr_DefaultAdapter
{
  private JTable component;
  
  public BindExpr_JTableAdapter()
  {
    super();
    component = new JTable();
  }
 
  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    TableModel tm = component.getModel();
    int i = 0;
    String temp;
    ZDeclList result = expr.getZDeclList();
    result.clear();
    for (i = 0; i < tm.getRowCount(); i++) {
      temp = (String) tm.getValueAt(i, 0);
      ZDeclName name = factory.createZDeclName(temp);
      temp = (String) tm.getValueAt(i, 1);
      Expr value = GaffeFactory.decodeExpr(temp);
      result.add((Decl) factory.createConstDecl(name, value));
    }
    expr.setDeclList(result);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    ZDeclList declList = expr.getZDeclList();
    Object[][] dataModel = new Object[declList.size()][2];
    int i = 0;
    for (Decl decl : declList) {
      ConstDecl tempDecl = (ConstDecl) decl;
      dataModel[i][0] = tempDecl.getZDeclName().toString();
      dataModel[i][1] = GaffeFactory.encodeExpr(tempDecl.getExpr());
      i++;
    }
    component.setModel(new DefaultTableModel(dataModel, new String[]{
        "Key", "Value"}));
    return component;
  }
}
