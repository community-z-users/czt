
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Toolkit;

import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JPanel;

import net.sourceforge.czt.animation.control.CloseDialogListener;
import net.sourceforge.czt.animation.control.FitInListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class WrapperDialog extends JDialog
{
  protected JComponent target;
  protected JButton okButton;
  protected JButton clButton;
  protected JPanel buttonPane;
  
  /**
   * Constructor
   * @param schemaName
   * @param parent
   */
  public WrapperDialog(JComponent tar)
  {
    target = tar;
    buttonPane = new JPanel(new FlowLayout(FlowLayout.CENTER));
    okButton = new JButton("Tab..");
    clButton = new JButton("Close");
    okButton.addActionListener(new FitInListener(this));
    clButton.addActionListener(new CloseDialogListener(this));
    buttonPane.add(okButton);
    buttonPane.add(clButton);
    Dimension position = Toolkit.getDefaultToolkit().getScreenSize();
    this.setLocation((int)(position.getWidth()/2 -150),(int)(position.getHeight()/2-100));
    this.setLayout(new BorderLayout());
    this.add(target, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
    this.setTitle(target.getName());
    this.pack();
  }

  /**
   * @return the target wrapped in.
   */
  public JComponent getTarget()
  {
    return target;
  }
}
