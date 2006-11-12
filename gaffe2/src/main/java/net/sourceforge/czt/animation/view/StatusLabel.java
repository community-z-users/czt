/**
 * 
 */

package net.sourceforge.czt.animation.view;

import javax.swing.JLabel;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StatusLabel extends JLabel
{
  private static StatusLabel currentLabel;

  public StatusLabel()
  {
    super();
    currentLabel = this;
  }

  /**
   * @param message The message to set.
   */
  public static void setMessage(String message)
  {
    currentLabel.setText(message);
  }

}
