
package net.sourceforge.czt.animation.common.evaluator;

import java.net.URL;
import java.util.HashMap;

import net.sourceforge.czt.animation.model.EvalResult;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public interface Evaluator
{
  /**
   * Initialize the evaluator after user has confirmed schema types 
   * @param file url
   * @param initSchema name
   * @return
   */
  public EvalResult initialize(URL file, String initSchema);

  /**
   * Evaluate a given operation
   * @param name the name of the schema
   * @param input the input binding map contains state and input variables
   * @return an output which has implemented an evalResult interface
   */
  public EvalResult activateSchema(String name, HashMap<String, Expr> input);
}