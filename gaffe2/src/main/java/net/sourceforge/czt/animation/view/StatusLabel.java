/**
 * 
 */

package net.sourceforge.czt.animation.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.JLabel;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StatusLabel extends JLabel implements PropertyChangeListener
{
  /**
   * Constructor
   * @param message
   */
  public StatusLabel(String message)
  {
    super(message);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    StepTree tree = GaffeUtil.getStepTree();
    this.setText("Result: " + tree.getIndex() + "/" + (tree.size() - 1));
  }
}
