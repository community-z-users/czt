
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
public class ChangeStepListener implements ActionListener
{
  private JPopupMenu source;      // The popupMenu displaying available operations

  /**
   * Constructor
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
    StepTree tree = GaffeUtil.getStepTree();
    String operation = "";
    if (arg0.getSource() instanceof JMenuItem) {
      JMenuItem item = (JMenuItem) arg0.getSource();
      operation = item.getText();
      source.setVisible(false);
    }
    else {
      operation = "back";
    }
    if (!tree.moveTo(operation)) {
      System.out.println("Change to step " + operation + " has failed..");
    }
  }
}
