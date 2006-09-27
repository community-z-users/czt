
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.HashMap;

import javax.swing.JComponent;
import javax.swing.JTree;
import javax.swing.tree.TreePath;

import net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.view.InputDialog;
import net.sourceforge.czt.gaffe2.animation.view.VariablePane;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class OperationListener extends MouseAdapter
{
  private JTree tree;
  
  /**
   * @param schemaName
   * @param parent
   */
  public OperationListener(JComponent component)
  {
    tree = (JTree) component;
  }

  /* (non-Javadoc)
   * @see java.awt.event.MouseListener#mousePressed(java.awt.event.MouseEvent)
   */
  public void mousePressed(MouseEvent e)
  {
    // TODO Auto-generated method stub
    Analyzer analyzer = GaffeFactory.getAnalyzer();
    int selRow = tree.getRowForLocation(e.getX(), e.getY());
    TreePath selPath = tree.getPathForLocation(e.getX(), e.getY());
    if (selRow != -1) {
      if (e.getClickCount() == 1) {
        //
      }
      else if (e.getClickCount() == 2) {
        String schemaName = selPath.getLastPathComponent().toString();
        InputDialog id = new InputDialog(schemaName);
        VariablePane inputPane = id.getInputPane();
        HashMap<String, Expr> input = analyzer.getVariableMap(schemaName,
            "input");
        inputPane.setComponentMap(GaffeFactory.exprMapToComponentMap(null,
            input));
        inputPane.update();
        id.pack();
        id.setModal(true);
        id.setVisible(true);
      }
    }
  }
}
