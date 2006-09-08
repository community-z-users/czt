
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import net.sourceforge.czt.gaffe2.animation.view.MainFrame;
import net.sourceforge.czt.gaffe2.animation.view.OutputDialog;
import net.sourceforge.czt.gaffe2.animation.view.VariablePane;

/**
 * @author Linan Zhang
 *
 */
public class FitInListener implements ActionListener
{
  OutputDialog od;

  public FitInListener(OutputDialog od)
  {
    this.od = od;
  }

  public void actionPerformed(ActionEvent arg0)
  {
    VariablePane vp = od.getOutputPane();
    MainFrame.getRightSplit().setBottomComponent(vp);
    MainFrame.getRightSplit().setDividerLocation(0.8);
    od.remove(vp);
    od.dispose();
  }

}
