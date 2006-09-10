
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;

/**
 * @author Linan Zhang
 *
 */
public class RefExpr_JTextFieldAdapter extends AdapterDefaultImpl
{
  public RefExpr_JTextFieldAdapter(){
    super();
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
    if (origin == null) {
      origin = new JTextField();
    }
    JTextField component = (JTextField) origin;
    RefExpr value = (RefExpr) expr;
    component.setText(value.getZRefName().getWord());
    return component;
  }

  public Object encodeExpr(Expr expr){
    RefExpr value = (RefExpr) expr;
    return value.getZRefName().getWord();
  }
  
  public Expr decodeExpr(Object code){
    String value = (String) code;
    return factory.createRefExpr(factory.createZRefName(value));
  }
}
