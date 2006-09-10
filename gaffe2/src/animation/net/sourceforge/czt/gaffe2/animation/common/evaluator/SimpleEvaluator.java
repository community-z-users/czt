
package net.sourceforge.czt.gaffe2.animation.common.evaluator;

import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.EvalResult;
import net.sourceforge.czt.gaffe2.animation.model.SimpleResult;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZExprList;
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
      String newName = ((RefExpr) input.get("name?")).getZRefName().getWord();
      String newDate = ((RefExpr) input.get("date?")).getZRefName().getWord();
      birthday = (BindExpr) input.get("birthday");
      known = (SetExpr) input.get("known");

      ZExprList oldList = known.getZExprList();
      ZExprList exprList = factory.createZExprList();
      for (Expr expr : oldList) {
        RefExpr value = (RefExpr) expr;
        if (value.getZRefName().getWord().equals(newName)) {
          output.put("known'", known);
          output.put("birthday'", birthday);
          resultList.add(output);
          return new SimpleResult(resultList);
        }
        exprList.add(value);
      }
      exprList.add(factory.createRefExpr(factory.createZRefName(newName)));

      ZDeclList bindList = factory.createZDeclList(birthday.getZDeclList());
      ZDeclName declname = factory.createZDeclName(newName);
      RefExpr value = factory.createRefExpr(factory.createZRefName(newDate));
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
      RefExpr value2 = factory.createRefExpr(factory.createZRefName(newDate+"_2"));
      newList2.add((Decl) factory.createConstDecl(declname2, value2));
      Expr birthdayPrime2 = factory.createBindExpr(newList2);
      output2.put("known'", knownPrime2);
      output2.put("birthday'", birthdayPrime2);
      resultList.add(output2);
      //
      return new SimpleResult(resultList);
    }
    else if (name.equals("FindBirthday")) {
      Expr output_date = factory.createRefExpr(factory.createZRefName("Not found"));
      String input_name = ((RefExpr) input.get("name?")).getZRefName().getWord();
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
      Expr output_name = factory.createRefExpr(factory.createZRefName("Not found"));
      String input_date = ((RefExpr) input.get("date?")).getZRefName().getWord();
      birthday = (BindExpr) input.get("birthday");
      known = (SetExpr) input.get("known");
      ZDeclList declList = birthday.getZDeclList();
      for (Decl decl : declList) {
        ConstDecl constDecl = (ConstDecl) decl;
        if (constDecl.getExpr().toString().equals(input_date)) {
          output_name = factory.createRefExpr(factory.createZRefName(constDecl.getZDeclName()));
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
  /*
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
  */
}
