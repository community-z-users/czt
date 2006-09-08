/**
 * 
 */

package net.sourceforge.czt.gaffe2.animation.view;

import java.beans.PropertyChangeEvent;
import java.util.HashMap;

import javax.swing.JComponent;
import javax.swing.border.TitledBorder;

import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class OutputPane extends VariablePane
{
  private static OutputPane currentPane;

  /**
   * 
   */
  public OutputPane()
  {
    super();
    currentPane = this;
    this.setBorder(new TitledBorder("Output"));
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    HashMap<String, JComponent> newMap = null;
    Step source = (Step) arg0.getSource();
    HashMap<String, Expr> result = source.getResultSelected();
    newMap = GaffeFactory.exprMapToComponentMap(newMap, result);
    contentPane.removeAll();
    componentMap.clear();
    for (String key : result.keySet()) {
      if (key.endsWith("!")) {
        componentMap.put(key, newMap.get(key));
        this.add(key, newMap.get(key));
      }
    }
    contentPane.validate();
    this.repaint();
  }

  /**
   * @return Returns the currentPane.
   */
  public static OutputPane getCurrentPane()
  {
    return currentPane;
  }

}
