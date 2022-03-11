
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextArea;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZString;

/**
 * @author Linan Zhang
 *
 */
public class BindExpr_JTextAreaAdapter extends BindExpr_DefaultAdapter
{
  private JTextArea component;              // Display the BindExpr as a TextArea

  /**
   * Constructor
   */
  public BindExpr_JTextAreaAdapter()
  {
    super();
    component = new JTextArea("");
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#componentToData(javax.swing.JComponent)
   */
  public Expr getExpr()
  {
    String text = component.getText();
    String r[] = text.split(System.getProperty("line.separator"));
    int i = 0;
    String temp[];
    ZDeclList result = expr.getZDeclList();
    result.clear();
    for (i = 0; i < r.length; i++) {
      temp = r[i].split(ZString.MAPSTO);
      ZName name = factory.createZName(temp[0]);
      Expr value = (temp.length > 1) ? GaffeUtil.decodeExpr(temp[1]) : null;
      result.add((Decl) factory.createConstDecl(name, value));
    }
    expr.setDeclList(result);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#dataToComponent(javax.swing.JComponent, net.sourceforge.czt.z.ast.Expr)
   */
  public JComponent getComponent()
  {
    ZDeclList declList = expr.getZDeclList();
    component.setText("");
    String temp = "";
    //int i = 0;
    for (Decl decl : declList) {
      ConstDecl tempDecl = (ConstDecl) decl;
      temp = tempDecl.getZName().toString();
      temp += ZString.MAPSTO;
      temp += GaffeUtil.encodeExpr(tempDecl.getExpr());
      temp += System.getProperty("line.separator");
      component.append(temp);
      //i++;
    }
    return component;
  }
}
