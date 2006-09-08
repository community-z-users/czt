
package net.sourceforge.czt.gaffe2.animation.view;

import javax.swing.border.TitledBorder;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StatePane extends VariablePane
{
  private static StatePane currentPane;

  /**
   * 
   */
  public StatePane()
  {
    super();
    currentPane = this;
    this.setBorder(new TitledBorder("State"));
  }

  /**
   * @return Returns the currentStatePane.
   */
  public static StatePane getCurrentPane()
  {
    return currentPane;
  }
}
