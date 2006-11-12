/**
 * 
 */

package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.animation.view.MainFrame;
import net.sourceforge.czt.animation.view.OperationPane;
import net.sourceforge.czt.animation.view.OutputPane;
import net.sourceforge.czt.animation.view.StatePane;
import net.sourceforge.czt.animation.view.StatusLabel;
import net.sourceforge.czt.animation.view.ToolBar;

/**
 * @author Linan Zhang
 *
 */
public class CloseItemListener implements ActionListener
{
  /**
   * 
   */
  public CloseItemListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    StatePane.getCurrentPane().reset();
    OutputPane.getCurrentPane().reset();
    OperationPane.getCurrentPane().reset();
    ToolBar.getCurrentToolBar().reset();
    StepTree.reset();
    MainFrame.getFrameSplit().setVisible(false);
    GaffeFactory.getZLive().getSectionManager().reset();
    StatusLabel.setMessage("Ready");
  }

}
