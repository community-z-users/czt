/**
 * 
 */

package net.sourceforge.czt.animation.control;

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
import javax.swing.border.TitledBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

import net.sourceforge.czt.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.common.factory.GaffeUI;
import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.EvalResult;
import net.sourceforge.czt.animation.model.Step;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.animation.view.VariablePane;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class GaffeLoadListener implements ActionListener
{
  DefaultTreeModel evaluatingTree;

  /**
   * Constructor
   */
  public GaffeLoadListener()
  {
    evaluatingTree = new DefaultTreeModel(new Step("Root", null));
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    JFileChooser fileChooser = new JFileChooser("load ..");
    if (fileChooser.showOpenDialog(null) == JFileChooser.APPROVE_OPTION) {
      this.load(fileChooser.getSelectedFile());
    }
  }

  /**
   * Load a saved Gaffe File
   * @param file
   */
  public void load(File file)
  {
    try {
      XMLDecoder e = new XMLDecoder(new BufferedInputStream(
          new FileInputStream(file)));

      try {
        //ReInitialize Analyzer
        String specFile = (String) e.readObject();
        String stateSchemaName = (String) e.readObject();
        String initSchemaName = (String) e.readObject();
        Analyzer analyzer = GaffeFactory.getAnalyzer();
        analyzer.initialize(new File(specFile));
        //Reset UI
        GaffeUI.resetAll();
  
        //ReInitialise Evaluator
        VariablePane statePane = new VariablePane();
        statePane.setBorder(new TitledBorder("state"));
        statePane.setName(file.getName());
        GaffeUI.getMainFrame().tab(statePane,"RT");
        GaffeUI.setStatePane(statePane);
        HashMap<String, Expr> state = analyzer.getVariableMap(stateSchemaName,
            "state");
        state = GaffeUtil.prime(state);
        statePane.setComponentMap(GaffeUtil.createComponentMap(state));
        Evaluator evaluator = GaffeFactory.getEvaluator();
        EvalResult results = evaluator.initialize(analyzer.getSpecURL(),
            initSchemaName);
        Step step = new Step(initSchemaName, results);
        Step evaluatingRoot = (Step) evaluatingTree.getRoot();
        evaluatingRoot.add(step);
        System.out.println("Loading file.. " + file.getName());
        /*---------------------------------------------*/
  
        // Load SchemaTree
        DefaultTreeModel schemaTree = (DefaultTreeModel) e.readObject();
        GaffeUI.getOperationPane().add(new JTree(schemaTree));
        /*---------------------------------------------*/
  
        // Load StepTree
        StepTree tree = (StepTree) e.readObject();
        GaffeUtil.addStepTree("default", tree);
        tree.setStateSchemaName(stateSchemaName);
        tree.setInitSchemaName(initSchemaName);
        tree.addPropertyChangeListener(statePane);
        tree.addPropertyChangeListener(GaffeUI.getToolBar());
        Step root = (Step) tree.getRoot();
        restore(root);
        tree.setStep(root);
        /*---------------------------------------------*/
      } finally {
        e.close();
      }
      GaffeUI.getMainFrame().reset();
      System.out.println("File: " + file.getName() + "loaded!");
    } catch (IOException ioex) {
      ioex.printStackTrace();
      System.out.println("File: " + file.getName() + "load failed!");
    }
  }

  /**
   * Restore all steps information by navigation through the tree
   * @param parent
   */
  public void restore(DefaultMutableTreeNode parent)
  {
    Step child;
    for (int i = 0; i < parent.getChildCount(); i++) {
      child = (Step) parent.getChildAt(i);
      child.restore();
      restore(child);
    }
  }
}
