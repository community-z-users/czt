
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.HashMap;

import javax.swing.JComboBox;
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
import net.sourceforge.czt.gaffe2.animation.view.StatePane;
import net.sourceforge.czt.gaffe2.animation.view.StatusLabel;
import net.sourceforge.czt.gaffe2.animation.view.ToolBar;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class SchemaTypeListener implements ActionListener
{
  private String stateSchemaName;

  private String initSchemaName;

  private MainFrame parent;

  private ArrayList<JComboBox> result;

  private Analyzer analyzer;

  /**
   * @param parent
   * @param source
   * @param result
   */
  public SchemaTypeListener(ArrayList<JComboBox> result)
  {
    this.result = result;
    parent = MainFrame.getMainFrame();
    analyzer = GaffeFactory.getAnalyzer();
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    this.schemaTree();
    this.initialize();
    MainFrame.getFrameSplit().setVisible(true);
    parent.validate();
    MainFrame.getFrameSplit().setDividerLocation(0.2);
    MainFrame.getRightSplit().setDividerLocation(0.8);
  }

  /**
   * 
   */
  private void schemaTree()
  {
    OperationPane operationPane = OperationPane.getCurrentPane();
    String schemaName = "";
    DefaultMutableTreeNode root = new DefaultMutableTreeNode(analyzer
        .getSpecURL().getFile());
    DefaultMutableTreeNode state = new DefaultMutableTreeNode("State");
    DefaultMutableTreeNode initial = new DefaultMutableTreeNode("Initial");
    DefaultMutableTreeNode operation = new DefaultMutableTreeNode("Operation");
    DefaultMutableTreeNode ignore = new DefaultMutableTreeNode("Ignore");
    for (JComboBox choice : result) {
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
   * 
   */
  private void initialize()
  {
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
    StepTree.add(step);
    StatusLabel.setMessage("Result: " + step.getIndex() + "/"
        + (step.size() - 1));
  }
}