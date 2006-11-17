
package net.sourceforge.czt.animation.view;

import java.awt.BorderLayout;
import java.beans.PropertyChangeEvent;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.control.ChangeNodeListener;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StepTreePane extends JScrollPane
{
  private JPanel contentPane;

  private JTree component;

  /**
   * 
   */
  public StepTreePane()
  {
    component = new JTree(GaffeUtil.getStepTree());
    component.addMouseListener(new ChangeNodeListener(component));
    contentPane = new JPanel(new BorderLayout());
    contentPane.add(component, BorderLayout.CENTER);
    this.getViewport().setView(contentPane);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeListener#propertyChange(java.beans.PropertyChangeEvent)
   */
  public void propertyChange(PropertyChangeEvent arg0)
  {
    component.setModel((StepTree) arg0.getSource());
    this.validate();
  }
}
