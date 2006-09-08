
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.animation.eval.GivenValue;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class GivenValueAdapter implements Adapter
{
  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#componentToData(javax.swing.JComponent)
   */
  public Expr componentToData(JComponent jc)
  {
    JTextField component = (JTextField) jc;
    return new GivenValue(component.getText());
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
    GivenValue givenValue = (GivenValue) expr;
    component.setText(givenValue.getValue());
    return component;
  }

}
