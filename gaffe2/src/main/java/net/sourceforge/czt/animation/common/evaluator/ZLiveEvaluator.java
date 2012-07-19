
package net.sourceforge.czt.animation.common.evaluator;

import java.net.URL;
import java.util.HashMap;
import java.util.Scanner;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.model.EvalResult;
import net.sourceforge.czt.animation.model.EvalSetResult;
import net.sourceforge.czt.animation.view.MessagePane;
import net.sourceforge.czt.animation.view.WrapperDialog;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class ZLiveEvaluator implements Evaluator
{
  private static ZLive zlive_;                     // The ZLive unique ref

  private static Factory factory_;                 // The factory from ZLive

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator#initialize(java.net.URL, java.lang.String)
   */
  public EvalResult initialize(URL file, String initSchema)
  {
    // ZLive should already been initialized in Analyzer,
    // Or else you should initialize it here.
    zlive_ = GaffeFactory.getZLive();
    factory_ = GaffeFactory.getFactory();
    return this.activateSchema(initSchema, new HashMap<String, Expr>());
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator#activateSchema(java.lang.String, java.util.HashMap)
   */
  public EvalResult activateSchema(String name, HashMap<String, Expr> input)
  {
    // TODO Auto-generated method stub
    try {
      ZDeclList declList = factory_.createZDeclList();
      for (String key : input.keySet()) {
        ZName declName = factory_.createZName(key);
        ConstDecl constDecl = factory_
            .createConstDecl(declName, input.get(key));
        declList.add(constDecl);
      }
      BindExpr inputExpr = factory_.createBindExpr(declList);
      System.out.println("\nReady to evaluate schema: " + name);
      System.out.println("Input: " + zlive_.termToString(inputExpr));
      System.out
          .println("******************Evaluation BEGIN!**********************************");
      Expr schema = zlive_.schemaExpr(name);
      Envir env = new Envir().plusAll(inputExpr);
      EvalSet result = (EvalSet) zlive_.evalTerm(true, schema, env).getResult();
      System.out
          .println("******************Evaluation SUCCESS!********************************");
      System.out
          .println("Whether has a result: " + result.iterator().hasNext());
      System.out.println("Output: "
          + zlive_.termToString(result.iterator().next()));
      return new EvalSetResult(result);
    } catch (CommandException commex) {
      System.out
          .println("******************Evaluation Failed!*********************************");
      new WrapperDialog(new MessagePane(commex));
      return null;
    } catch (EvalException evalex) {
      System.out
          .println("******************Evaluation Failed!*********************************");
      new WrapperDialog(new MessagePane(evalex));
      System.out.println("\n Would like to use manual Evaluator to proceed? 'y' or 'n'");
      Scanner scanner = new Scanner(System.in);
      if (scanner.nextByte()=='Y') {
        //
      }
      scanner.close();
      return null;
    }
  }

}
