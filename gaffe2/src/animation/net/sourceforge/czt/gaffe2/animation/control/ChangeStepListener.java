
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;

import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;
import net.sourceforge.czt.gaffe2.animation.view.StatusLabel;

/**
 * @author Linan Zhang
 *
 */
public class ChangeStepListener implements ActionListener
{
  private JPopupMenu source;

  /**
   * @param parent
   * @param action
   */
  public ChangeStepListener(JPopupMenu source)
  {
    this.source = source;
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    String operation = "";
    if (arg0.getSource() instanceof JMenuItem) {
      JMenuItem item = (JMenuItem) arg0.getSource();
      operation = item.getText();
      source.setVisible(false);
    }
    else {
      operation = "back";
    }
    if (!StepTree.moveTo(operation)) {
      StatusLabel.setMessage("Change to step " + operation + " has failed..");
    }
    else {
      Step step = StepTree.getCurrentStep();
      StatusLabel.setMessage("Result: " + step.getIndex() + "/"
          + (step.size() - 1));
    }
  }
}
