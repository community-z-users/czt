
package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Toolkit;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;

import net.sourceforge.czt.gaffe2.animation.control.FitInListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class OutputDialog extends JDialog
{
  private VariablePane outputPane;

  /**
   * @param schemaName
   * @param parent
   */
  public OutputDialog(VariablePane vp)
  {
    outputPane = vp;

    JPanel buttonPane = new JPanel(new FlowLayout(FlowLayout.CENTER));
    JButton okButton = new JButton("OK      ");
    okButton.addActionListener(new FitInListener(this));
    buttonPane.add(okButton);

    Dimension position = Toolkit.getDefaultToolkit().getScreenSize();
    this.setLocation((int) (position.getWidth() / 2 - 150), (int) (position
        .getHeight() / 2 - 100));
    this.setLayout(new BorderLayout());
    this.add(outputPane, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
    this.setTitle("Output");
    this.pack();
  }

  /**
   * @return Returns the outputPane.
   */
  public VariablePane getOutputPane()
  {
    return outputPane;
  }
}
