/**
 * 
 */

package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.XMLDecoder;
import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.HashMap;

import javax.swing.JFileChooser;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

import net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.EvalResult;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;
import net.sourceforge.czt.gaffe2.animation.view.MainFrame;
import net.sourceforge.czt.gaffe2.animation.view.OperationPane;
import net.sourceforge.czt.gaffe2.animation.view.OutputPane;
import net.sourceforge.czt.gaffe2.animation.view.StatePane;
import net.sourceforge.czt.gaffe2.animation.view.StatusLabel;
import net.sourceforge.czt.gaffe2.animation.view.ToolBar;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class LoadItemListener implements ActionListener
{
  DefaultTreeModel evaluatingTree;
  /**
   * 
   */
  public LoadItemListener()
  {
    evaluatingTree = new DefaultTreeModel(new Step("Root",null));
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    MainFrame parent = MainFrame.getMainFrame();
    JFileChooser fileChooser = new JFileChooser("load ..");
    if (fileChooser.showOpenDialog(parent) == JFileChooser.APPROVE_OPTION) {
      this.load(fileChooser.getSelectedFile());
    }
  }

  /**
   * @param file
   */
  public void load(File file)
  {
    try {
      XMLDecoder e = new XMLDecoder(new BufferedInputStream(
          new FileInputStream(file)));
 
      //ReInitialize Analyzer
      String specFile = (String)e.readObject();
      String stateSchemaName = (String)e.readObject();
      String initSchemaName = (String)e.readObject();
      Analyzer analyzer = GaffeFactory.getAnalyzer();
      analyzer.initialize(new File(specFile));
      
      //Reset UI
      StatePane.getCurrentPane().reset();
      OutputPane.getCurrentPane().reset();
      OperationPane.getCurrentPane().reset();
      ToolBar.getCurrentToolBar().reset();
      MainFrame.getMainFrame().validate();
      MainFrame.getRightSplit().setDividerLocation(0.8);
      MainFrame.getFrameSplit().setDividerLocation(0.2);
      MainFrame.getFrameSplit().setVisible(true);
      
      //ReInitialise Evaluator
      StatePane statePane = StatePane.getCurrentPane();
      HashMap<String, Expr> state = analyzer.getVariableMap(stateSchemaName,
          "state");
      state = GaffeFactory.prime(state);
      statePane.setComponentMap(GaffeFactory.exprMapToComponentMap(null, state));
      Evaluator evaluator = GaffeFactory.getEvaluator();
      EvalResult results = evaluator.initialize(analyzer.getSpecURL(),
          initSchemaName);
      Step step = new Step(initSchemaName,results);
      step.addPropertyChangeListener(statePane);
      step.addPropertyChangeListener(ToolBar.getCurrentToolBar());
      Step evaluatingRoot = (Step)evaluatingTree.getRoot();
      evaluatingRoot.add(step);
      StatusLabel.setMessage("Loading file.. "+file.getName());
      /*---------------------------------------------*/
      
      // Load SchemaTree
      DefaultTreeModel schemaTree = (DefaultTreeModel) e.readObject();
      OperationPane.getCurrentPane().add(new JTree(schemaTree));
      /*---------------------------------------------*/
      
      // Load StepTree
      DefaultTreeModel stepTree = (DefaultTreeModel) e.readObject();
      StepTree.setStepTree(stepTree);
      DefaultMutableTreeNode root = (Step) stepTree.getRoot();
      restore(root);
      StepTree.setCurrentStep((Step)root.getChildAt(0));
      /*---------------------------------------------*/
      
      e.close();
      StatusLabel.setMessage("File: "+file.getName()+"loaded!");
    } catch (IOException ioex) {
      ioex.printStackTrace();
      StatusLabel.setMessage("File: "+file.getName()+"not loaded!");
    }
  }
  
  public void restore(DefaultMutableTreeNode parent){
    Step child;
    for (int i = 0; i<parent.getChildCount();i++){
      child =  (Step)parent.getChildAt(i);  
      child.restore();
      restore(child);
    }
  }
}
