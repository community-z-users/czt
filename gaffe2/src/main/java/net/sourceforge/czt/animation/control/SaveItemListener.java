/**
 * 
 */

package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.XMLEncoder;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import javax.swing.JFileChooser;
import javax.swing.JTree;
import javax.swing.tree.DefaultTreeModel;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.animation.view.MainFrame;
import net.sourceforge.czt.animation.view.OperationPane;

/**
 * @author Linan Zhang
 *
 */
public class SaveItemListener implements ActionListener
{
  /**
   * 
   */
  public SaveItemListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    MainFrame parent = MainFrame.getMainFrame();
    JFileChooser fileChooser = new JFileChooser("Save ..");
    if (fileChooser.showSaveDialog(parent) == JFileChooser.APPROVE_OPTION) {
      this.save(fileChooser.getSelectedFile());
    }
  }

  public void save(File file)
  {
    //  TODO Auto-generated method stub
    DefaultTreeModel target_operation = (DefaultTreeModel) ((JTree) OperationPane
        .getCurrentPane().getComponent()).getModel();
    DefaultTreeModel target_stepTree = StepTree.getStepTree();
    try {
      XMLEncoder e = new XMLEncoder(new BufferedOutputStream(
          new FileOutputStream(file)));
      //Save specURL
      e.writeObject(GaffeFactory.getAnalyzer().getSpecURL().getFile());
      //Save stateSchemaName
      e.writeObject(StepTree.getStateSchemaName());
      //Save initSchemaName
      e.writeObject(StepTree.getInitSchemaName());
      //Save SchemaTree
      e.writeObject(target_operation);
      //Save StepTree
      e.writeObject(target_stepTree);
      e.close();
    } catch (IOException ioex) {
      ioex.printStackTrace();
    }
  }

  /* Mirror Tree constructor . Not used yet. But works well.
   public DefaultTreeModel visitTree(DefaultTreeModel tree){
   DefaultMutableTreeNode root = (DefaultMutableTreeNode)tree.getRoot();
   DefaultMutableTreeNode newRoot = visit(root);
   DefaultTreeModel newTree = new DefaultTreeModel(newRoot);
   return newTree;
   }
   
   public DefaultMutableTreeNode visit(DefaultMutableTreeNode parent){
   DefaultMutableTreeNode child;
   DefaultMutableTreeNode newParent = ((Step) parent);
   for (int i = 0; i<parent.getChildCount();i++){
   child =  (DefaultMutableTreeNode)parent.getChildAt(i);  
   newParent.add(visit(child));
   }
   return newParent;
   }
   */
}
