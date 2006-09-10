
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import java.util.HashMap;

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
public class BindExpr_JTableAdapter extends AdapterDefaultImpl
{
  public BindExpr_JTableAdapter()
  {
    super();
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
      RefExpr value = factory.createRefExpr(factory.createZRefName(temp));
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
        dataModel[i][1] = ((RefExpr) tempDecl.getExpr()).getZRefName().getWord();
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

  /**
   * @param expr
   * @return
   */
  public Object encodeExpr(Expr expr){
    BindExpr bindExpr = (BindExpr) expr;
    ZDeclList declList = bindExpr.getZDeclList();
    
    HashMap<String,String> code = new HashMap<String,String>();
    String key;
    String value;
    for (Decl decl : declList) {
      ConstDecl tempDecl = (ConstDecl) decl;
      key = tempDecl.getZDeclName().toString();
      value = ((RefExpr) tempDecl.getExpr()).getZRefName().getWord();
      code.put(key,value);
    }
    return code;
    
  }
  
  /**
   * @param value
   * @return
   */
  @SuppressWarnings("unchecked")
  public Expr decodeExpr(Object value)
  {
    HashMap<String,String> code = (HashMap<String,String>)(value);
    ZDeclList result = factory.createZDeclList();
    for (String key : code.keySet()) {
      ZDeclName name = factory.createZDeclName(key);
      RefExpr expr = factory.createRefExpr(factory.createZRefName(code.get(key)));
      result.add((Decl) factory.createConstDecl(name, expr));
    }
    return factory.createBindExpr(result);
  }
}
