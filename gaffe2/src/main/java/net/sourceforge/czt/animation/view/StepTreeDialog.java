
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;

import javax.swing.JDialog;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StepTreeDialog extends JDialog
{
  /**
   * @param stp
   */
  public StepTreeDialog(StepTreePane stp)
  {
    this.setLayout(new BorderLayout());
    this.add(stp, BorderLayout.CENTER);
    this.setLocationRelativeTo(MainFrame.getMainFrame());
    this.setTitle("Step Tree");
    this.setSize(800, 600);
    this.setVisible(true);
  }
}
