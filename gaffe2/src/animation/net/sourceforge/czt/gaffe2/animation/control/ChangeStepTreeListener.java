
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.JComponent;
import javax.swing.JTree;
import javax.swing.tree.TreePath;

import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
public class ChangeStepTreeListener extends MouseAdapter
{
  private JTree tree;

  /**
   * @param schemaName
   * @param parent
   */
  public ChangeStepTreeListener(JComponent component)
  {
    tree = (JTree) component;
  }

  /* (non-Javadoc)
   * @see java.awt.event.MouseListener#mousePressed(java.awt.event.MouseEvent)
   */
  public void mousePressed(MouseEvent e)
  {
    // TODO Auto-generated method stub
    int selRow = tree.getRowForLocation(e.getX(), e.getY());
    TreePath selPath = tree.getPathForLocation(e.getX(), e.getY());
    if (selRow != -1) {
      if (e.getClickCount() == 1) {
        //
      }
      else if (e.getClickCount() == 2) {
        Step node = (Step) selPath.getLastPathComponent();
        StepTree.setCurrentStep(node);
        node.firePropertyChange("index", -1, 0);
      }
    }
  }
}
