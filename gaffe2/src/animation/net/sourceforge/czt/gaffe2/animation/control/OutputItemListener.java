
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.gaffe2.animation.view.MainFrame;
import net.sourceforge.czt.gaffe2.animation.view.OutputDialog;
import net.sourceforge.czt.gaffe2.animation.view.OutputPane;

/**
 * @author Linan Zhang
 *
 */
public class OutputItemListener implements ActionListener
{
  public OutputItemListener()
  {
  }

  public void actionPerformed(ActionEvent arg0)
  {
    OutputDialog od = new OutputDialog(OutputPane.getCurrentPane());
    od.pack();
    od.setAlwaysOnTop(true);
    od.setLocationRelativeTo(MainFrame.getMainFrame());
    od.setVisible(true);
  }

}
