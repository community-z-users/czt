/**
 * 
 */

package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.common.factory.GaffeUI;

/**
 * @author Linan Zhang
 *
 */
public class ResetListener implements ActionListener
{
  /**
   * 
   */
  public ResetListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    GaffeUI.resetAll();
    GaffeFactory.getZLive().getSectionManager().reset();
  }

}
