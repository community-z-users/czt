
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.view.MainFrame;

/**
 * @author Linan Zhang
 *
 */
public class ExitItemListener implements ActionListener
{
  /**
   * @param parent
   */
  public ExitItemListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    MainFrame.getMainFrame().dispose();
    System.exit(0);
  }

}
