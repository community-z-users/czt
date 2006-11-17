
package net.sourceforge.czt.animation.control;

import java.awt.Dimension;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.view.StepTreeDialog;

/**
 * @author Linan Zhang
 *
 */
public class ShowStepTreeDialogListener implements ActionListener
{
  public ShowStepTreeDialogListener()
  {
  }

  public void actionPerformed(ActionEvent arg0)
  {
    StepTreeDialog std = new StepTreeDialog(GaffeUI.getStepTreePane());
    std.setAlwaysOnTop(true);
    Dimension dim1 = Toolkit.getDefaultToolkit().getScreenSize();
    Dimension dim2 = std.getSize();
    std.setLocation((dim1.width - dim2.width) / 2,
        (dim1.height - dim2.height) / 2);
    std.setVisible(true);
  }

}
