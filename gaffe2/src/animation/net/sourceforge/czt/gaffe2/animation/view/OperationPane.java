
package net.sourceforge.czt.gaffe2.animation.view;

import java.awt.BorderLayout;

import javax.swing.JComponent;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import net.sourceforge.czt.gaffe2.animation.control.OperationListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class OperationPane extends JScrollPane
{
  private JPanel contentPane;

  private static OperationPane currentPane;

  /**
   * 
   */
  public OperationPane()
  {
    contentPane = new JPanel(new BorderLayout());
    this.getViewport().setView(contentPane);
    currentPane = this;
  }

  /**
   * @param component
   */
  public void add(JComponent component)
  {
    component.addMouseListener(new OperationListener(component));
    contentPane.add(component, BorderLayout.CENTER);
  }

  /**
   * @return Returns the currentOperationPane.
   */
  public static OperationPane getCurrentPane()
  {
    return currentPane;
  }
}
