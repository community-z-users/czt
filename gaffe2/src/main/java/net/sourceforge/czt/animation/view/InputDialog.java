
package net.sourceforge.czt.animation.view;

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
    okButton.setText("Evaluate");
    clButton.setText("Cancel  ");
    okButton.removeAll();
    okButton.addActionListener(new EvaluateListener());
  }
}
