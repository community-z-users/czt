
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;

import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;

/**
 * @author Linan Zhang
 *
 */
public class BindExpr_JTableAdapter extends BindExpr_DefaultAdapter
{
  public BindExpr_JTableAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#componentToData(javax.swing.JComponent)
   */
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
      RefExpr value = factory.createRefExpr(factory.createZRefName(temp));
      result.add((Decl) factory.createConstDecl(name, value));
    }
    return factory.createBindExpr(result);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#dataToComponent(javax.swing.JComponent, net.sourceforge.czt.z.ast.Expr)
   */
  public JComponent dataToComponent(JComponent origin, Expr expr)
  {
    BindExpr bindExpr = (BindExpr) expr;
    ZDeclList declList = bindExpr.getZDeclList();
    JTable component = (origin==null)? new JTable():(JTable)origin;
    Object[][] dataModel = new Object[declList.size()][2];
    int i = 0;
    for (Decl decl : declList) {
      ConstDecl tempDecl = (ConstDecl) decl;
      dataModel[i][0] = tempDecl.getZDeclName().toString();
      dataModel[i][1] = ((RefExpr) tempDecl.getExpr()).getZRefName().getWord();
      i++;
    }
    component.setModel(new DefaultTableModel(dataModel, new String[]{
        "Key", "Value"}));
    return component;
  }
}
