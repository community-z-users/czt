
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeUI;

/**
 * @author Linan Zhang
 *
 */
public class ExitListener implements ActionListener
{
  /**
   * Constructor
   * @param parent
   */
  public ExitListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    GaffeUI.getMainFrame().dispose();
    System.exit(0);
  }

}
