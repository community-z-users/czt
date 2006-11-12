
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.model.Step;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.animation.view.StatusLabel;

/**
 * @author Linan Zhang
 *
 */
public class ChangeResultListener implements ActionListener
{
  private int offset;

  /**
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
    Step step = StepTree.getCurrentStep();
    int newValue = step.getIndex() + offset;
    if (!step.changeIndex(newValue)) {
      StatusLabel.setMessage("Change to result " + newValue + " has failed..");
    }
    else {
      StatusLabel.setMessage("Result: " + step.getIndex() + "/"
          + (step.size() - 1));
    }
  }
}
