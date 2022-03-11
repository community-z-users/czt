
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.view.WrapperDialog;

/**
 * @author Linan Zhang
 *
 */
public class ShowOutputDialogListener implements ActionListener
{
  /**
   * Constructor
   */
  public ShowOutputDialogListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    WrapperDialog od = new WrapperDialog(GaffeUI.getOutputPane());
    od.pack();
    od.setAlwaysOnTop(true);
    od.setLocationRelativeTo(GaffeUI.getMainFrame());
    od.setVisible(true);
  }

}
