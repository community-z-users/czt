
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JComponent;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.view.WrapperDialog;

/**
 * @author Linan Zhang
 *
 */
public class FitInListener implements ActionListener
{
  private WrapperDialog od;          // The dialog acts as the wrapper for the pane inside.

  /**
   * Constructor
   * @param od
   */
  public FitInListener(WrapperDialog od)
  {
    this.od = od;
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    JComponent vp = od.getTarget();
    // Release the target back into MainFrame as a tabbed Pane.
    GaffeUI.getMainFrame().tab(vp,"RT");
    od.remove(vp);
    od.dispose();
  }

}
