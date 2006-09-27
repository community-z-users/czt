
package net.sourceforge.czt.gaffe2.animation.common.factory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.JComponent;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.BindExpr_JTableAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.BindExpr_JTextAreaAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.NumExpr_JTextFieldAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.RefExpr_JTextAreaAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.RefExpr_JTextFieldAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.SetExpr_JListAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.SetExpr_JTextAreaAdapter;
import net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.gaffe2.animation.common.analyzer.ZLiveAnalyzer;
import net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.gaffe2.animation.common.evaluator.ZLiveEvaluator;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
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

  private static Map<String,Adapter> adapterMap = new HashMap<String,Adapter>();
  
  private static Map<String,List<Adapter>> availableMap = new HashMap<String,List<Adapter>>();
  
  private static GaffeFactory gaffeFactory = new GaffeFactory();
  
  /**
   * No instance, solid
   */
  public GaffeFactory()
  {
    System.out.println("GaffeFactory .. Initializing");
    
    //Preparation
    List<Adapter> numExprList = new ArrayList<Adapter>();
    numExprList.add(new NumExpr_JTextFieldAdapter());
    
    List<Adapter> refExprList = new ArrayList<Adapter>();
    refExprList.add(new RefExpr_JTextFieldAdapter());
    refExprList.add(new RefExpr_JTextAreaAdapter());
    
    List<Adapter> bindExprList = new ArrayList<Adapter>();
    bindExprList.add(new BindExpr_JTableAdapter());
    bindExprList.add(new BindExpr_JTextAreaAdapter());
    
    List<Adapter> setExprList = new ArrayList<Adapter>();
    setExprList.add(new SetExpr_JListAdapter());
    setExprList.add(new SetExpr_JTextAreaAdapter());
    
    //Initialize avaiable adapters
    availableMap.put("NumExprImpl",numExprList);
    availableMap.put("RefExprImpl",refExprList);
    availableMap.put("BindExprImpl",bindExprList);
    availableMap.put("SetExprImpl",setExprList);
    
    //Setting default adapter configuration
    adapterMap.put("NumExprImpl",numExprList.get(0));
    adapterMap.put("RefExprImpl",refExprList.get(0));
    adapterMap.put("BindExprImpl",bindExprList.get(0));
    adapterMap.put("SetExprImpl",setExprList.get(0));
  }
  
  /**
   * @param expr
   * @return
   */
  public static Object encodeExpr(Expr expr){
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
    //String name of section
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
  
  public static Adapter getAdapter(Expr expr)
  {
    return adapterMap.get(expr.getClass().getSimpleName());
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
  public static HashMap<String, JComponent> exprMapToComponentMap(
      HashMap<String, JComponent> origin, HashMap<String, Expr> result)
  {
    if (origin == null) {
      origin = new HashMap<String, JComponent>();
    }
    Adapter adapter;
    for (String key : result.keySet()) {
      Expr expr = result.get(key);
      adapter = GaffeFactory.getAdapter(expr);
      origin.put(key, adapter.dataToComponent(origin.get(key), expr));
    }
    return origin;
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
   * @return Returns the adapterMap.
   */
  public static Map<String, Adapter> getAdapterMap()
  {
    return adapterMap;
  }

  /**
   * @return Returns the availableMap.
   */
  public static Map<String, List<Adapter>> getAvailableMap()
  {
    return availableMap;
  }
}
