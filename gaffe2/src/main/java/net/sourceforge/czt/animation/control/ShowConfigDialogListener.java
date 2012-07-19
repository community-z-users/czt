
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.view.ConfigDialog;

/**
 * @author Linan Zhang
 *
 */
public class ShowConfigDialogListener implements ActionListener
{

  /**
   * Constructor
   */
  public ShowConfigDialogListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    new ConfigDialog();
  }

}
