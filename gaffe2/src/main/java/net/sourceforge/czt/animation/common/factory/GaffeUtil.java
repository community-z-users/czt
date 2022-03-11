
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
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.model.StepTree;
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
import net.sourceforge.czt.z.util.ZChar;

/**
 * @author Linan Zhang
 *
 */
public class GaffeUtil
{
  private static String name;                                                                // The current session Name

  private static Map<String, StepTree> sessionMap = new HashMap<String, StepTree>();         // The seesion Map hold Name - > StepTree binding

  private static Map<String, Class<?>> customMap = new HashMap<String, Class<?>>();                // The customer specified UI Map (VariableName-->Adapter)

  private static Map<String, List<Class<?>>> availableMap = new HashMap<String, List<Class<?>>>(); // The avaiable UI Map           (VariableName-->Available Adapter List>

  // No instance, solid
  private GaffeUtil()
  {
  }

  /**
   * Load all adapters at the application begins. ? better way of doing this, any suggestion?
   */
  public static void loadExprMap()
  {
    //Preparation
    List<Class<?>> numExprList = new ArrayList<Class<?>>();
    numExprList.add(NumExpr_DefaultAdapter.class);
    numExprList.add(NumExpr_JSpinnerAdapter.class);

    List<Class<?>> refExprList = new ArrayList<Class<?>>();
    refExprList.add(RefExpr_DefaultAdapter.class);
    refExprList.add(RefExpr_JTextAreaAdapter.class);

    List<Class<?>> bindExprList = new ArrayList<Class<?>>();
    bindExprList.add(BindExpr_JTableAdapter.class);
    bindExprList.add(BindExpr_JTextAreaAdapter.class);

    List<Class<?>> setExprList = new ArrayList<Class<?>>();
    setExprList.add(SetExpr_JListAdapter.class);
    setExprList.add(SetExpr_JTextAreaAdapter.class);

    //Initialize avaiable adapters
    availableMap.put(NumExprImpl.class.getSimpleName(), numExprList);
    availableMap.put(RefExprImpl.class.getSimpleName(), refExprList);
    availableMap.put(BindExprImpl.class.getSimpleName(), bindExprList);
    availableMap.put(SetExprImpl.class.getSimpleName(), setExprList);
  }

  /**
   * Encode the expr to a String
   * @param expr
   * @return
   */
  public static String encodeExpr(Expr expr)
  {
    return GaffeFactory.getZLive().termToString(expr, Markup.LATEX);
  }

  /**
   * Decode the String back to a Expr
   * @param value
   * @return
   */
  public static Expr decodeExpr(Object value)
  {
    ZLive zLive = GaffeFactory.getZLive();
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

  /**
   * Add "'" after each variable in the target Map given. Then they are "primed"
   * @param target
   * @return
   */
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
   * Initialize the component Map which holds all the variables being displayed
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
   * Get the customer specified UI component Adapter for Exprs
   * @return the customMap.
   */
  public static Map<String, Class<?>> getCustomMap()
  {
    return customMap;
  }

  /**
   * Get the Available UI component adpaters Map for Exprs
   * @return the availableMap.
   */
  public static Map<String, List<Class<?>>> getAvailableMap()
  {
    return availableMap;
  }

  /**
   * Get the current session based StepTree
   * @param name
   * @return the stepTree selected
   */
  public static StepTree getStepTree()
  {
    return sessionMap.get(name);
  }

  /**
   * Add a new StepTree session based
   * @param name
   * @param stepTree
   */
  public static void addStepTree(String name, StepTree stepTree)
  {
    sessionMap.put(name, stepTree);
    GaffeUtil.name = name;
  }

  /**
   * Get the current session Name
   * @return the name.
   */
  public static String getName()
  {
    return name;
  }

  /**
   * Set the current session Name
   * @param name The name to set.
   */
  public static void setName(String name)
  {
    GaffeUtil.name = name;
  }
}
