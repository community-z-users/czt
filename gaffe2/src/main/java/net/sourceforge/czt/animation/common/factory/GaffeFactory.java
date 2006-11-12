
package net.sourceforge.czt.animation.common.factory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.animation.common.adapter.Adapter;
import net.sourceforge.czt.animation.common.adapter.BindExpr_JTableAdapter;
import net.sourceforge.czt.animation.common.adapter.BindExpr_JTextAreaAdapter;
import net.sourceforge.czt.animation.common.adapter.NumExpr_DefaultAdapter;
import net.sourceforge.czt.animation.common.adapter.NumExpr_JSpinnerAdapter;
import net.sourceforge.czt.animation.common.adapter.RefExpr_DefaultAdapter;
import net.sourceforge.czt.animation.common.adapter.RefExpr_JTextAreaAdapter;
import net.sourceforge.czt.animation.common.adapter.SetExpr_JListAdapter;
import net.sourceforge.czt.animation.common.adapter.SetExpr_JTextAreaAdapter;
import net.sourceforge.czt.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.animation.common.analyzer.ZLiveAnalyzer;
import net.sourceforge.czt.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.animation.common.evaluator.ZLiveEvaluator;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.impl.BindExprImpl;
import net.sourceforge.czt.z.impl.NumExprImpl;
import net.sourceforge.czt.z.impl.RefExprImpl;
import net.sourceforge.czt.z.impl.SetExprImpl;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZChar;

/**
 * @author Linan Zhang
 *
 */
public class GaffeFactory
{
  private static ZLive zLive = new ZLive();

  private static Analyzer analyzer = new ZLiveAnalyzer();

  private static Evaluator evaluator = new ZLiveEvaluator();

  private static Map<String, Class> customMap = new HashMap<String, Class>();

  private static Map<String, List<Class>> availableMap = new HashMap<String, List<Class>>();

  private static GaffeFactory gaffeFactory = new GaffeFactory();

  /**
   * No instance, solid
   */
  public GaffeFactory()
  {
    System.out.println("GaffeFactory .. Initializing");

    //Preparation
    List<Class> numExprList = new ArrayList<Class>();
    numExprList.add(NumExpr_DefaultAdapter.class);
    numExprList.add(NumExpr_JSpinnerAdapter.class);

    List<Class> refExprList = new ArrayList<Class>();
    refExprList.add(RefExpr_DefaultAdapter.class);
    refExprList.add(RefExpr_JTextAreaAdapter.class);

    List<Class> bindExprList = new ArrayList<Class>();
    bindExprList.add(BindExpr_JTableAdapter.class);
    bindExprList.add(BindExpr_JTextAreaAdapter.class);

    List<Class> setExprList = new ArrayList<Class>();
    setExprList.add(SetExpr_JListAdapter.class);
    setExprList.add(SetExpr_JTextAreaAdapter.class);

    //Initialize avaiable adapters
    availableMap.put(NumExprImpl.class.getSimpleName(), numExprList);
    availableMap.put(RefExprImpl.class.getSimpleName(), refExprList);
    availableMap.put(BindExprImpl.class.getSimpleName(), bindExprList);
    availableMap.put(SetExprImpl.class.getSimpleName(), setExprList);
  }

  /**
   * @param expr
   * @return
   */
  public static Object encodeExpr(Expr expr)
  {
    return zLive.printTerm(expr, Markup.LATEX);
  }

  /**
   * @param value
   * @return
   */
  public static Expr decodeExpr(Object value)
  {
    Source newSource = new StringSource(value.toString());
    System.out.println("someee... " + value.toString());
    newSource.setMarkup(Markup.LATEX);
    SectionManager sectman = zLive.getSectionManager();
    try {
      Expr expr = ParseUtils.parseExpr(newSource, zLive.getCurrentSection(),
          sectman);
      return expr;
    } catch (IOException ex) {
      ex.printStackTrace();
      return null;
    } catch (CommandException ex) {
      ex.printStackTrace();
      return null;
    }
  }

  public static HashMap<String, Expr> prime(HashMap<String, Expr> target)
  {
    HashMap<String, Expr> result = new HashMap<String, Expr>();
    Expr expr;
    for (String key : target.keySet()) {
      expr = target.get(key);
      result.put(key + ZChar.PRIME, expr);
    }
    return result;
  }

  /**
   * @param origin
   * @param result
   * @return
   */
  public static HashMap<String, Adapter> createComponentMap(
      HashMap<String, Expr> data)
  {
    HashMap<String, Adapter> result = new HashMap<String, Adapter>();
    Adapter adapter;
    for (String key : data.keySet()) {
      try {
        adapter = (Adapter) customMap.get(key).newInstance();
        adapter.setExpr(data.get(key));
        result.put(key, adapter);
      } catch (InstantiationException instex) {
        instex.printStackTrace();
      } catch (IllegalAccessException acceex) {
        acceex.printStackTrace();
      }
    }
    return result;
  }

  /**
   * @return
   */
  public static Analyzer getAnalyzer()
  {
    return analyzer;
  }

  /**
   * @return
   */
  public static Evaluator getEvaluator()
  {
    return evaluator;
  }

  /**
   * @return
   */
  public static Factory getFactory()
  {
    return zLive.getFactory();
  }

  /**
   * @return Returns the zLive.
   */
  public static ZLive getZLive()
  {
    return zLive;
  }

  /**
   * @return Returns the gaffeFactory.
   */
  public static GaffeFactory getGaffeFactory()
  {
    return gaffeFactory;
  }

  /**
   * @return Returns the customMap.
   */
  public static Map<String, Class> getCustomMap()
  {
    return customMap;
  }

  /**
   * @return Returns the availableMap.
   */
  public static Map<String, List<Class>> getAvailableMap()
  {
    return availableMap;
  }
}
