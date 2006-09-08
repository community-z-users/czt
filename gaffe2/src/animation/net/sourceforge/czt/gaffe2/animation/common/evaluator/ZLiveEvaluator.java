
package net.sourceforge.czt.gaffe2.animation.common.evaluator;

import java.net.URL;
import java.util.HashMap;

import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.EvalResult;
import net.sourceforge.czt.gaffe2.animation.model.EvalSetResult;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class ZLiveEvaluator implements Evaluator
{
  private ZLive zlive_;

  private Factory factory_;

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator#initialize(java.net.URL, java.lang.String)
   */
  public EvalResult initialize(URL file, String initSchema)
  {
    // TODO Auto-generated method stub
    try {
      zlive_ = new ZLive();
      factory_ = GaffeFactory.getFactory();
      Source src = new FileSource(file.getFile());
      src.setMarkup(Markup.LATEX);
      Key key = new Key("real", Source.class);
      zlive_.getSectionManager().put(key, src);
      zlive_.setCurrentSection("real");
      return this.activateSchema(initSchema, null);
    } catch (CommandException comex) {
      comex.printStackTrace();
      return null;
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator#activateSchema(java.lang.String, java.util.HashMap)
   */
  public EvalResult activateSchema(String name, HashMap<String, Expr> input)
  {
    // TODO Auto-generated method stub
    ZDeclList declList = factory_.createZDeclList();
    for (String key : input.keySet()) {
      DeclName declName = factory_.createZDeclName(key);
      ConstDecl constDecl = factory_.createConstDecl(declName, input.get(key));
      declList.add(constDecl);
    }
    BindExpr inputExpr = factory_.createBindExpr(declList);
    try {
      EvalSet result = (EvalSet) zlive_.evalSchema(name, inputExpr);
      return new EvalSetResult(result);
    } catch (CommandException commex) {
      commex.printStackTrace();
      return null;
    }
  }

}
