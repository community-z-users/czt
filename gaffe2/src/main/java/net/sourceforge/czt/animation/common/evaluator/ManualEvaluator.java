package net.sourceforge.czt.animation.common.evaluator;

import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.model.EvalResult;
import net.sourceforge.czt.animation.model.EvalSetResult;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class ManualEvaluator implements Evaluator
{

  /**
   * Constructor
   */
  public ManualEvaluator()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.common.evaluator.Evaluator#initialize(java.net.URL, java.lang.String)
   */
  public EvalResult initialize(URL file, String initSchema)
  {
    return this.activateSchema(initSchema, new HashMap<String, Expr>());
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.common.evaluator.Evaluator#activateSchema(java.lang.String, java.util.HashMap)
   */
  public EvalResult activateSchema(String name, HashMap<String, Expr> input)
  {
    System.out.println("\n Manual Evaluator Start!" +
                       "\n Please provide the result BindExpr");
    BindExpr result = null; 
    Scanner scanner = new Scanner(System.in);
    result = (BindExpr)GaffeUtil.decodeExpr(scanner.nextLine());
    List<Expr> resultList = new ArrayList<Expr>(); 
    resultList.add(result);
    scanner.close();
    return new EvalSetResult(resultList);
  }

}
