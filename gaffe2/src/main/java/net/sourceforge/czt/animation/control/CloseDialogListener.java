
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JDialog;

/**
 * @author Linan Zhang
 *
 */
public class CloseDialogListener implements ActionListener
{
  private JDialog source;            // The source dialog going to be disposed

  /**
   * Constructor
   * @param source
   */
  public CloseDialogListener(JDialog source)
  {
    this.source = source;
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent ae)
  {
    source.dispose();
  }
}
