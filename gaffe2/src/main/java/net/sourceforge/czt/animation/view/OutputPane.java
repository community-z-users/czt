/**
 * 
 */

package net.sourceforge.czt.animation.view;

import java.beans.PropertyChangeEvent;
import java.util.HashMap;

import javax.swing.border.TitledBorder;

import net.sourceforge.czt.animation.common.adapter.Adapter;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.ZString;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class OutputPane extends VariablePane
{
  /**
   * Constructor
   */
  public OutputPane()
  {
    super();
    this.setBorder(new TitledBorder("Output"));
    this.setName("Output");
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    StepTree source = (StepTree) arg0.getSource();
    HashMap<String, Expr> result = source.getStep().getResultSelected();
    contentPane.removeAll();
    componentMap.clear();
    Adapter adapter = null;
    for (String key : result.keySet()) {
      // Filtering the variables with the "!" as the tail
      if (key.endsWith(ZString.OUTSTROKE)) {
        adapter = componentMap.get(key);
        adapter.setExpr(result.get(key));
        this.add(key, adapter.getComponent());
      }
    }
    contentPane.validate();
    this.repaint();
  }
}
