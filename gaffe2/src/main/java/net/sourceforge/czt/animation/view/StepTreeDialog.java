
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Toolkit;

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
    this.setTitle("Step Tree");
    this.setSize(800, 600);
    Dimension dim1 = Toolkit.getDefaultToolkit().getScreenSize();
    Dimension dim2 = this.getSize();
    this.setLocation((dim1.width - dim2.width) / 2,
        (dim1.height - dim2.height) / 2);
    this.setVisible(true);
  }
}
