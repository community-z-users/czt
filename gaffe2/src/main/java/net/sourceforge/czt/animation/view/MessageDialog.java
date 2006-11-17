/**
 * 
 */

package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Toolkit;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import net.sourceforge.czt.animation.control.DisposeDialogListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class MessageDialog extends JDialog
{
  private JTextArea messageText;

  /**
   * 
   */
  public MessageDialog()
  {
    super();
    messageText = new JTextArea();
    messageText.setEditable(false);
    JButton okButton = new JButton("Ok");
    okButton.addActionListener(new DisposeDialogListener(this));
    JPanel buttonPanel = new JPanel();
    buttonPanel.setLayout(new FlowLayout(FlowLayout.CENTER));
    buttonPanel.add(okButton);
    this.setLayout(new BorderLayout());
    this.add(new JScrollPane(messageText), BorderLayout.CENTER);
    this.add(buttonPanel, BorderLayout.SOUTH);
    this.setTitle("Message!");
    this.setSize(640, 320);
    Dimension dim1 = Toolkit.getDefaultToolkit().getScreenSize();
    Dimension dim2 = this.getSize();
    this.setLocation((dim1.width - dim2.width) / 2,
        (dim1.height - dim2.height) / 2);
    this.setModal(true);
  }

  /**
   * @param message
   */
  public MessageDialog(String message)
  {
    this();
    this.setMessage(message);
    this.setVisible(true);
  }

  /**
   * @param ex
   */
  public MessageDialog(Exception ex)
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
