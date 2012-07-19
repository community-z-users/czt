
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
public class ChangeResultListener implements ActionListener
{
  private int offset;              // How many steps be back(-) or forward(+)

  /**
   * Constructor
   * @param parent
   * @param action
   */
  public ChangeResultListener(int offset)
  {
    this.offset = offset;
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    StepTree tree = GaffeUtil.getStepTree();
    int newValue = tree.getIndex() + offset;
    if (!tree.changeIndex(newValue)) {
      System.out.println("Change to result " + newValue + " has failed..");
    }
  }
}
