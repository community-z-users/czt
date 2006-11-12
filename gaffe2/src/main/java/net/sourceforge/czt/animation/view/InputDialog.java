
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Toolkit;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;

import net.sourceforge.czt.animation.control.CancelListener;
import net.sourceforge.czt.animation.control.EvaluateListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class InputDialog extends JDialog
{
  private VariablePane inputPane;

  private String schemaName;

  /**
   * @param schemaName
   * @param parent
   */
  public InputDialog(String schemaName)
  {
    this.schemaName = schemaName;
    inputPane = new VariablePane();

    JPanel buttonPane = new JPanel();
    JButton evalButton = new JButton("Evaluate");
    JButton cancelButton = new JButton("Cancel  ");
    evalButton.addActionListener(new EvaluateListener(this));
    cancelButton.addActionListener(new CancelListener(this));
    buttonPane.setLayout(new FlowLayout(FlowLayout.CENTER));
    buttonPane.add(evalButton);
    buttonPane.add(cancelButton);

    Dimension position = Toolkit.getDefaultToolkit().getScreenSize();
    this.setLayout(new BorderLayout());
    this.add(inputPane, BorderLayout.CENTER);
    this.add(buttonPane, BorderLayout.SOUTH);
    this.setTitle(schemaName + " ... Input");
    this.pack();
    this.setLocation((int) (position.getWidth() / 2 - 150), (int) (position
        .getHeight() / 2 - 100));
  }

  /**
   * @return
   */
  public String getSchemaName()
  {
    return schemaName;
  }

  /**
   * @return
   */
  public VariablePane getInputPane()
  {
    return inputPane;
  }

}
