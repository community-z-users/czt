
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;

import net.sourceforge.czt.animation.control.ChangeStepTreeListener;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StepTreePane extends JScrollPane
{
  private JPanel contentPane;

  private static StepTreePane currentPane;

  /**
   * 
   */
  public StepTreePane()
  {
    JTree component = new JTree(StepTree.getStepTree());
    component.addMouseListener(new ChangeStepTreeListener(component));
    contentPane = new JPanel(new BorderLayout());
    contentPane.add(component, BorderLayout.CENTER);
    this.getViewport().setView(contentPane);
    currentPane = this;
  }

  /**
   * @return Returns the currentPane.
   */
  public static StepTreePane getCurrentPane()
  {
    return currentPane;
  }

}
