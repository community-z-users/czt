
package net.sourceforge.czt.animation.control;

import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.JComponent;
import javax.swing.JTree;
import javax.swing.tree.TreePath;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.Step;
import net.sourceforge.czt.animation.model.StepTree;

/**
 * @author Linan Zhang
 *
 */
public class ChangeNodeListener extends MouseAdapter
{
  private JTree tree;           // The UI displaying StepTree

  /**
   * @param schemaName
   * @param parent
   */
  public ChangeNodeListener(JComponent component)
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
        Step node = (Step) selPath.getLastPathComponent();
        StepTree stepTree = GaffeUtil.getStepTree();
        stepTree.setStep(node);
        tree.expandPath(selPath);
      }
      else if (e.getClickCount() == 2) {
        // Nothing to do
      }
    }
  }
}
