
package net.sourceforge.czt.animation.view;

import javax.swing.JButton;

import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.control.CloseDialogListener;
import net.sourceforge.czt.animation.control.EvaluateListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class InputDialog extends WrapperDialog
{
  /**
   * Constructor
   * @param schemaName
   */
  public InputDialog(String schemaName)
  {
    super(new VariablePane());
    target.setName(schemaName);
    setTitle(schemaName);
    okButton = new JButton("Evaluate");
    clButton.setText("Cancel  ");
    okButton.addActionListener(new EvaluateListener());
    okButton.addActionListener(new CloseDialogListener(this));
    buttonPane.removeAll();
    buttonPane.add(okButton);
    buttonPane.add(clButton);
    GaffeUI.setInputPane((VariablePane)this.getTarget());
  }
}
