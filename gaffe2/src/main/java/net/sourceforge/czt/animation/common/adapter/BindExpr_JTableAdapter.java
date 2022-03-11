
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;

/**
 * @author Linan Zhang
 *
 */
public class BindExpr_JTableAdapter extends BindExpr_DefaultAdapter
{
  private JTable component;             // Display the bindExpr as a Table

  /**
   * Constructor
   */
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
      ZName name = factory.createZName(temp);
      temp = (String) tm.getValueAt(i, 1);
      Expr value = GaffeUtil.decodeExpr(temp);
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
      dataModel[i][0] = tempDecl.getZName().toString();
      dataModel[i][1] = GaffeUtil.encodeExpr(tempDecl.getExpr());
      i++;
    }
    component.setModel(new DefaultTableModel(dataModel, new String[]{"Key",
        "Value"}));
    return component;
  }
}
