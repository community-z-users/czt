/**
 * 
 */

package net.sourceforge.czt.animation.view;

import javax.swing.JScrollPane;
import javax.swing.JTextArea;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class MessagePane extends JScrollPane
{
  private JTextArea messageText;

  /**
   * Constructor
   */
  public MessagePane()
  {
    super();
    messageText = new JTextArea();
    messageText.setEditable(false);
    this.getViewport().setView(messageText);
    this.setSize(640, 320);
    this.setName("Message");
  }

  /**
   * @param message
   */
  public MessagePane(String message)
  {
    this();
    this.setMessage(message);
    this.setVisible(true);
  }

  /**
   * @param ex
   */
  public MessagePane(Exception ex)
  {
    this();
    this.setMessage(ex.getMessage());
    for (StackTraceElement ste : ex.getStackTrace()) {
      messageText.append("\n  ......" + ste.toString());
    }
    this.setVisible(true);
  }

  /**
   * @param message
   */
  public void setMessage(String message)
  {
    messageText.setText(message);
  }

}
