
package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public interface Adapter
{
  // Retrieve data from input component
  public Expr componentToData(JComponent jc);

  // Update component with changed data
  public JComponent dataToComponent(JComponent origin, Expr expr);

}
