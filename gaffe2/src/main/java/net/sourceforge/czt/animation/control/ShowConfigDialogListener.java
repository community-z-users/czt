
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.view.ConfigDialog;

public class ShowConfigDialogListener implements ActionListener
{

  public ShowConfigDialogListener()
  {
  }

  public void actionPerformed(ActionEvent arg0)
  {
    new ConfigDialog();
  }

}
