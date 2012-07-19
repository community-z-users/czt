
package net.sourceforge.czt.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;

import net.sourceforge.czt.animation.common.adapter.Adapter;
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
public class EvaluateListener implements ActionListener
{
  /**
   * Constructor
   * @param parent
   * @param ancestor
   */
  public EvaluateListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    Evaluator evaluator = GaffeFactory.getEvaluator();
    StepTree tree = GaffeUtil.getStepTree();
    VariablePane inputPane = GaffeUI.getInputPane();
    String schemaName = inputPane.getName();

    HashMap<String, Adapter> inputMap = inputPane.getComponentMap();
    HashMap<String, Expr> last = tree.getStep().getResultSelected();
    HashMap<String, Expr> input = GaffeFactory.getAnalyzer().getVariableMap(
        schemaName, "input");

    Adapter adapter = null;
    for (String key : inputMap.keySet()) {
      adapter = inputMap.get(key);
      input.put(key, adapter.getExpr());
    }
    //Remove prime for state variables
    Expr expr;
    for (String key : GaffeUI.getStatePane().getComponentMap().keySet()) {
      expr = last.get(key);
      input.put(key.substring(0, key.length() - 1), expr);
    }

    /***************************************/
    EvalResult results = evaluator.activateSchema(schemaName, input);
    /***************************************/

    tree.add(new Step(schemaName, results));
  }
}
