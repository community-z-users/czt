package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;


public class RefExpr_DefaultAdapter extends AdapterDefaultImpl
{

  public RefExpr_DefaultAdapter()
  {
    super();
    // TODO Auto-generated constructor stub
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#componentToData(javax.swing.JComponent)
   */
  public Expr componentToData(JComponent jc)
  {
    JTextField component = (JTextField) jc;
    return factory.createRefExpr(factory.createZRefName(component.getText()));
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#dataToComponent(javax.swing.JComponent, net.sourceforge.czt.z.ast.Expr)
   */
  public JComponent dataToComponent(JComponent origin, Expr expr)
  {
    JTextField component = (origin == null)? new JTextField():(JTextField) origin;
    RefExpr value = (RefExpr) expr;
    //ZExprList exprList = value.getZExprList();
    component.setText(value.getZRefName().getWord());
    return component;
  }
  
 /* public Object encodeExpr(Expr expr){
    RefExpr value = (RefExpr) expr;
    return value.getZRefName().getWord();
  }
  
  public Expr decodeExpr(Object code){
    String value = (String) code;
    return factory.createRefExpr(factory.createZRefName(value));
  }
  */
}
