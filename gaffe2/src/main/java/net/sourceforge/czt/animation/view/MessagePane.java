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
  private JTextArea messageText;      // The text displayed as message

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
   * Construct a message pane with a given message
   * @param message
   */
  public MessagePane(String message)
  {
    this();
    this.setMessage(message);
    this.setVisible(true);
  }

  /**
   * Construct a message pane with a throwed exception
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
   * Set the message for display
   * @param message
   */
  public void setMessage(String message)
  {
    messageText.setText(message);
  }

}
