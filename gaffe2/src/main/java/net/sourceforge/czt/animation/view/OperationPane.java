
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;

import javax.swing.JComponent;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import net.sourceforge.czt.animation.control.ShowInputDialogListener;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class OperationPane extends JScrollPane
{
  private JPanel contentPane;

  private JComponent component;

  /**
   * Constructor
   */
  public OperationPane()
  {
    contentPane = new JPanel(new BorderLayout());
    this.getViewport().setView(contentPane);
  }

  /**
   * Add a new component into the Pane.
   * @param component
   */
  public void add(JComponent component)
  {
    this.component = component;
    component.addMouseListener(new ShowInputDialogListener(component));
    contentPane.add(component, BorderLayout.CENTER);
  }

  /**
   * Reset the content pane.
   */
  public void reset()
  {
    contentPane.removeAll();
  }

  /**
   * @return the contentPane.
   */
  public JComponent getComponent()
  {
    return component;
  }
}
