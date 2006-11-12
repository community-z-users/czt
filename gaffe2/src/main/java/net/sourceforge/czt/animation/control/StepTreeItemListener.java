
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.view.MainFrame;
import net.sourceforge.czt.animation.view.StepTreeDialog;
import net.sourceforge.czt.animation.view.StepTreePane;

/**
 * @author Linan Zhang
 *
 */
public class StepTreeItemListener implements ActionListener
{
  public StepTreeItemListener()
  {
  }

  public void actionPerformed(ActionEvent arg0)
  {
    StepTreePane stp = new StepTreePane();
    StepTreeDialog std = new StepTreeDialog(stp);
    std.setAlwaysOnTop(true);
    std.setLocationRelativeTo(MainFrame.getMainFrame());
    std.setVisible(true);
  }

}
