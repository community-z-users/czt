
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JDialog;

/**
 * @author Linan Zhang
 *
 */
public class CancelListener implements ActionListener
{
  JDialog source;

  /**
   * @param source
   */
  public CancelListener(JDialog source)
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
