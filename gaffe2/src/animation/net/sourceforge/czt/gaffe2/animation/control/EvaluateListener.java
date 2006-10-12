
package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;

import net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter;
import net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.EvalResult;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;
import net.sourceforge.czt.gaffe2.animation.view.InputDialog;
import net.sourceforge.czt.gaffe2.animation.view.OutputPane;
import net.sourceforge.czt.gaffe2.animation.view.StatePane;
import net.sourceforge.czt.gaffe2.animation.view.StatusLabel;
import net.sourceforge.czt.gaffe2.animation.view.ToolBar;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class EvaluateListener implements ActionListener
{
  private String schemaName;

  private InputDialog parent;

  /**
   * @param parent
   * @param ancestor
   */
  public EvaluateListener(InputDialog parent)
  {
    this.parent = parent;
    schemaName = parent.getSchemaName();
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    Evaluator evaluator = GaffeFactory.getEvaluator();
    StatePane statePane = StatePane.getCurrentPane();
    OutputPane outputPane = OutputPane.getCurrentPane();
    ToolBar toolBar = ToolBar.getCurrentToolBar();

    HashMap<String, Adapter> inputMap = parent.getInputPane()
        .getComponentMap();
    HashMap<String, Expr> last = StepTree.getCurrentStep().getResultSelected();
    HashMap<String, Expr> input = GaffeFactory.getAnalyzer().getVariableMap(schemaName,"input");
    
    Adapter adapter = null;
    for (String key : inputMap.keySet()) {
      adapter = inputMap.get(key);
      input.put(key, adapter.getExpr());
    }
    //Remove prime for state variables
    Expr expr;
    for (String key : statePane.getComponentMap().keySet()) {
      expr = last.get(key);
      input.put(key.substring(0, key.length() - 1), expr);
    }

    /***************************************/
    EvalResult results = evaluator.activateSchema(schemaName, input);
    /***************************************/

    Step step = new Step(schemaName,results);
    step.addPropertyChangeListener(statePane);
    step.addPropertyChangeListener(outputPane);
    step.addPropertyChangeListener(toolBar);
    StepTree.add(step);
    parent.dispose();
    StatusLabel.setMessage("Result: " + step.getIndex() + "/"
        + (step.size() - 1));
  }
}
