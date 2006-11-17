
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Toolkit;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;

import net.sourceforge.czt.animation.control.DisposeDialogListener;
import net.sourceforge.czt.animation.control.EvaluateListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class InputDialog extends JDialog
{
  private VariablePane inputPane;

  /**
   * @param schemaName
   */
  public InputDialog(String schemaName)
  {
    inputPane = new VariablePane();
    inputPane.setName(schemaName);

    JPanel buttonPane = new JPanel();
    JButton evalButton = new JButton("Evaluate");
    JButton cancelButton = new JButton("Cancel  ");
    evalButton.addActionListener(new EvaluateListener());
    evalButton.addActionListener(new DisposeDialogListener(this));
    cancelButton.addActionListener(new DisposeDialogListener(this));
    buttonPane.setLayout(new FlowLayout(FlowLayout.CENTER));
    buttonPane.add(evalButton);
    buttonPane.add(cancelButton);

    this.setLayout(new BorderLayout());
    this.add(inputPane, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
    this.setTitle(schemaName + " ... Input");
    this.pack();
    Dimension dim1 = Toolkit.getDefaultToolkit().getScreenSize();
    Dimension dim2 = this.getSize();
    this.setLocation((dim1.width - dim2.width) / 2,
        (dim1.height - dim2.height) / 2);
  }

  /**
   * @return Returns the inputPane.
   */
  public VariablePane getInputPane()
  {
    return inputPane;
  }

}
