
package net.sourceforge.czt.gaffe2.animation.common.evaluator;

import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.swing.ListModel;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.animation.eval.GivenValue;
import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatDiscreteSet;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.EvalResult;
import net.sourceforge.czt.gaffe2.animation.model.SimpleResult;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class SimpleEvaluator implements Evaluator
{
  private SetExpr known;

  private BindExpr birthday;

  private static Factory factory;

  /**
   * 
   */
  public SimpleEvaluator()
  {
    factory = GaffeFactory.getFactory();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator#initialize(java.net.URL, java.lang.String)
   */
  public EvalResult initialize(URL file, String initSchema)
  {
    List<HashMap<String, Expr>> resultList = new ArrayList<HashMap<String, Expr>>();
    HashMap<String, Expr> output = new HashMap<String, Expr>();
    Expr knownPrime = factory.createSetExpr(factory.createZExprList());
    Expr birthdayPrime = factory.createBindExpr(factory.createZDeclList());

    output.put("known'", knownPrime);
    output.put("birthday'", birthdayPrime);
    resultList.add(output);
    return new SimpleResult(resultList);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator#activateSchema(java.lang.String, java.util.HashMap)
   */
  public EvalResult activateSchema(String name, HashMap<String, Expr> input)
  {
    List<HashMap<String, Expr>> resultList = new ArrayList<HashMap<String, Expr>>();
    HashMap<String, Expr> output = new HashMap<String, Expr>();

    if (name.equals("AddBirthday")) {
      String newName = ((GivenValue) input.get("name?")).getValue();
      String newDate = ((GivenValue) input.get("date?")).getValue();
      birthday = (BindExpr) input.get("birthday");
      known = (SetExpr) input.get("known");

      ZExprList oldList = known.getZExprList();
      ZExprList exprList = factory.createZExprList();
      for (Expr expr : oldList) {
        GivenValue givenValue = (GivenValue) expr;
        if (givenValue.getValue().equals(newName)) {
          output.put("known'", known);
          output.put("birthday'", birthday);
          resultList.add(output);
          return new SimpleResult(resultList);
        }
        exprList.add(givenValue);
      }
      exprList.add(new GivenValue(newName));

      ZDeclList bindList = factory.createZDeclList(birthday.getZDeclList());
      ZDeclName declname = factory.createZDeclName(newName);
      GivenValue value = new GivenValue(newDate);
      bindList.add((Decl) factory.createConstDecl(declname, value));

      Expr knownPrime = factory.createSetExpr(exprList);
      Expr birthdayPrime = factory.createBindExpr(bindList);
      output.put("known'", knownPrime);
      output.put("birthday'", birthdayPrime);
      resultList.add(output);
      // Another Result

      HashMap<String, Expr> output2 = new HashMap<String, Expr>();
      Expr knownPrime2 = factory.createSetExpr(exprList);
      ZDeclList newList2 = factory.createZDeclList(birthday.getZDeclList());
      ZDeclName declname2 = factory.createZDeclName(newName);
      GivenValue value2 = new GivenValue(newDate + "!!!!!!!");
      newList2.add((Decl) factory.createConstDecl(declname2, value2));
      Expr birthdayPrime2 = factory.createBindExpr(newList2);
      output2.put("known'", knownPrime2);
      output2.put("birthday'", birthdayPrime2);
      resultList.add(output2);
      //
      return new SimpleResult(resultList);
    }
    else if (name.equals("FindBirthday")) {
      Expr output_date = new GivenValue("Not found");
      String input_name = ((GivenValue) input.get("name?")).getValue();
      birthday = (BindExpr) input.get("birthday");
      known = (SetExpr) input.get("known");
      ZDeclList declList = birthday.getZDeclList();
      for (Decl decl : declList) {
        ConstDecl constDecl = (ConstDecl) decl;
        if (constDecl.getDeclName().toString().equals(input_name)) {
          output_date = constDecl.getExpr();
        }
      }
      output.put("known'", known);
      output.put("birthday'", birthday);
      output.put("date!", output_date);
      resultList.add(output);
      return new SimpleResult(resultList);
    }
    else if (name.equals("Remind")) {
      Expr output_name = new GivenValue("Not found");
      String input_date = ((GivenValue) input.get("date?")).getValue();
      birthday = (BindExpr) input.get("birthday");
      known = (SetExpr) input.get("known");
      ZDeclList declList = birthday.getZDeclList();
      for (Decl decl : declList) {
        ConstDecl constDecl = (ConstDecl) decl;
        if (constDecl.getExpr().toString().equals(input_date)) {
          output_name = new GivenValue(constDecl.getZDeclName().toString());
        }
      }
      output.put("known'", known);
      output.put("birthday'", birthday);
      output.put("card!", output_name);
      resultList.add(output);
      return new SimpleResult(resultList);
    }
    else {
      return null;
    }
  }

  /**
   * @param lm
   * @return
   */
  public EvalSet listModelToEvalSet(ListModel lm)
  {
    Envir env = new Envir();
    ArrayList<ZRefName> list = new ArrayList<ZRefName>();
    ZRefName setName = factory.createZRefName("NoName");
    ZRefName tempName = null;
    String element;
    for (int i = 0; i < lm.getSize(); i++) {
      element = (String) lm.getElementAt(i);
      tempName = factory.createZRefName(String.valueOf(element.hashCode()));
      env = env.plus(tempName, new GivenValue(element));
      list.add(tempName);
    }
    env = env.plus(setName, null);
    FlatDiscreteSet s = new FlatDiscreteSet(list, setName);
    s.inferBounds(new Bounds());
    Mode m = s.chooseMode(env);
    s.setMode(m);
    s.startEvaluation();
    s.nextEvaluation();
    return s;
  }

}
