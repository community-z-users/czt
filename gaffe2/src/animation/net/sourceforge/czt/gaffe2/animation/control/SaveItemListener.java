/**
 * 
 */

package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.XMLEncoder;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import javax.swing.JFileChooser;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;
import net.sourceforge.czt.gaffe2.animation.view.MainFrame;
import net.sourceforge.czt.z.ast.Expr;

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
    DefaultTreeModel target = StepTree.getStepTree();
    try {
      XMLEncoder e = new XMLEncoder(new BufferedOutputStream(
          new FileOutputStream(file)));
      e.writeObject(target);
      e.close();
    } catch (IOException ioex) {
      ioex.printStackTrace();
    }
  }

  public DefaultTreeModel getEncodableTree(DefaultTreeModel tree){
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
  
  public String toString(Expr expr){
    ZLive zLive = GaffeFactory.getZLive();
    return zLive.printTerm(expr);
  }
}
