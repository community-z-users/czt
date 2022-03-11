
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.UnsupportedEncodingException;
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.HashMap;

import javax.swing.JComboBox;
import javax.swing.JTree;
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
import net.sourceforge.czt.animation.view.MainFrame;
import net.sourceforge.czt.animation.view.OperationPane;
import net.sourceforge.czt.animation.view.StatusLabel;
import net.sourceforge.czt.animation.view.StepTreePane;
import net.sourceforge.czt.animation.view.ToolBar;
import net.sourceforge.czt.animation.view.VariablePane;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class InitializeListener implements ActionListener
{
  private String stateSchemaName;            // The state SchemaName

  private String initSchemaName;             // The init SchemaName

  private ArrayList<JComboBox<String>> result;       // The result schmaTypes chosed by user

  private Analyzer analyzer;                 // Hold the analyzer ref

  /**
   * Constructor
   * @param parent
   * @param source
   * @param result
   */
  public InitializeListener(ArrayList<JComboBox<String>> result)
  {
    this.result = result;
    analyzer = GaffeFactory.getAnalyzer();
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    GaffeUI.resetAll();
    this.schemaTree();
    this.initialize();
    MainFrame frame = GaffeUI.getMainFrame();
    frame.reset();
  }

  /**
   * Generating the SchemaTree, for user to select an operation and trigger them
   */
  private void schemaTree()
  {
    OperationPane operationPane = GaffeUI.getOperationPane();
    String schemaName = "";
    DefaultMutableTreeNode root;
    try {
      root = new DefaultMutableTreeNode(
        URLDecoder.decode(analyzer.getSpecURL().getFile(), "UTF-8"));
    } catch (UnsupportedEncodingException e) {
      throw new RuntimeException(e);
    }
    DefaultMutableTreeNode state = new DefaultMutableTreeNode("State");
    DefaultMutableTreeNode initial = new DefaultMutableTreeNode("Initial");
    DefaultMutableTreeNode operation = new DefaultMutableTreeNode("Operation");
    DefaultMutableTreeNode ignore = new DefaultMutableTreeNode("Ignore");
    for (JComboBox<String> choice : result) {
      schemaName = choice.getName();
      if (choice.getSelectedItem().equals("State")) {
        stateSchemaName = schemaName;
        state.add(new DefaultMutableTreeNode(schemaName));
      }
      else if (choice.getSelectedItem().equals("Initial")) {
        initSchemaName = schemaName;
        initial.add(new DefaultMutableTreeNode(schemaName));
      }
      else if (choice.getSelectedItem().equals("Operation")) {
        operation.add(new DefaultMutableTreeNode(schemaName));
      }
      else {
        ignore.add(new DefaultMutableTreeNode(schemaName));
      }
    }
    root.add(state);
    root.add(initial);
    root.add(operation);
    root.add(ignore);
    operationPane.add(new JTree(new DefaultTreeModel(root)));
  }

  /**
   * Initialize main state variable panes, initialize StepTree.
   * The initializaion is done by Evaluator, it acts as a Schema Operation
   */
  private void initialize()
  {
    VariablePane statePane = GaffeUI.getStatePane();
    VariablePane outputPane = GaffeUI.getOutputPane();
    ToolBar toolBar = GaffeUI.getToolBar();
    StatusLabel statusLabel = GaffeUI.getStatusLabel();
    StepTreePane stepTreePane = GaffeUI.getStepTreePane();

    HashMap<String, Expr> state = analyzer.getVariableMap(stateSchemaName,
        "state");
    state = GaffeUtil.prime(state);
    statePane.setComponentMap(GaffeUtil.createComponentMap(state));
    Evaluator evaluator = GaffeFactory.getEvaluator();
    EvalResult results = evaluator.initialize(analyzer.getSpecURL(),
        initSchemaName);
    Step step = new Step(initSchemaName, results);
    StepTree tree = new StepTree(step);
    GaffeUtil.addStepTree("default",tree);
    tree.addPropertyChangeListener(statePane);
    tree.addPropertyChangeListener(outputPane);
    tree.addPropertyChangeListener(toolBar);
    tree.addPropertyChangeListener(statusLabel);
    tree.addPropertyChangeListener(stepTreePane);
    tree.setStateSchemaName(stateSchemaName);
    tree.setInitSchemaName(initSchemaName);
    tree.firePropertyChange("step",-1,0);
  }
}