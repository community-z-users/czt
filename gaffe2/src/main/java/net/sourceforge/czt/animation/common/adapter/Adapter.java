
package net.sourceforge.czt.animation.common.adapter;

import javax.swing.JComponent;

import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public interface Adapter
{
  // Update component with changed data
  public void setExpr(Expr expr);

  // Retrieve data from input component
  public Expr getExpr();

  // Return the UI for current Data
  public JComponent getComponent();

  // An string representation of this adapter
  public String toString();
}
