
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.view.OutputDialog;

/**
 * @author Linan Zhang
 *
 */
public class ShowOutputDialogListener implements ActionListener
{
  public ShowOutputDialogListener()
  {
  }

  public void actionPerformed(ActionEvent arg0)
  {
    OutputDialog od = new OutputDialog(GaffeUI.getOutputPane());
    od.pack();
    od.setAlwaysOnTop(true);
    od.setLocationRelativeTo(GaffeUI.getMainFrame());
    od.setVisible(true);
  }

}
