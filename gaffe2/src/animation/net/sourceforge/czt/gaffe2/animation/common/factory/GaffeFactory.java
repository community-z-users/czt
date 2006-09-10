
package net.sourceforge.czt.gaffe2.animation.common.factory;

import java.util.ArrayList;
import java.util.HashMap;

import javax.swing.JComponent;
import javax.swing.JList;
import javax.swing.JTable;
import javax.swing.JTextField;

import net.sourceforge.czt.animation.eval.GivenValue;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.AdapterException;
import net.sourceforge.czt.gaffe2.animation.common.adapter.BindExpr_JTableAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.RefExpr_JTextFieldAdapter;
import net.sourceforge.czt.gaffe2.animation.common.adapter.SetExpr_JListAdapter;
import net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.gaffe2.animation.common.analyzer.SimpleAnalyzer;
import net.sourceforge.czt.gaffe2.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.gaffe2.animation.common.evaluator.SimpleEvaluator;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class GaffeFactory
{
  private static ZLive zLive = new ZLive();

  private static Adapter refExpr_adapter = new RefExpr_JTextFieldAdapter();

  private static Adapter setExpr_adapter = new SetExpr_JListAdapter();

  private static Adapter bindExpr_adapter = new BindExpr_JTableAdapter();

  private static Analyzer analyzer = new SimpleAnalyzer();

  private static Evaluator evaluator = new SimpleEvaluator();

  /**
   * No instance, solid
   */
  private GaffeFactory()
  {
  }

  /**
   * @param component
   * @return
   */
  public static Adapter getAdapter(JComponent component)
  {
    try {
      if (component instanceof JTable) {
        return bindExpr_adapter;
      }
      else if (component instanceof JList) {
        return setExpr_adapter;
      }
      else if (component instanceof JTextField) {
        return refExpr_adapter;
      }
      else if (component == null) {
        throw new AdapterException("Null JComponent ");
      }
      else {
        throw new AdapterException("Unsupported JComponent "
            + component.getClass().toString());
      }
    } catch (AdapterException adapter_ex) {
      adapter_ex.printStackTrace();
      return null;
    }
  }

  public static Adapter getAdapter(Expr expr)
  {
    try {
      if (expr instanceof BindExpr) {
        return bindExpr_adapter;
      }
      else if (expr instanceof SetExpr) {
        return setExpr_adapter;
      }
      else if (expr instanceof RefExpr) {
        return refExpr_adapter;
      }
      else if (expr == null) {
        throw new AdapterException("Null Expr ");
      }
      else {
        throw new AdapterException("Unsupported Expr "
            + expr.getClass().toString());
      }
    } catch (AdapterException adapter_ex) {
      adapter_ex.printStackTrace();
      return null;
    }
  }
  
  public static Adapter getAdapter(Object code)
  {
    try {
      if (code instanceof HashMap) {
        return bindExpr_adapter;
      }
      else if (code instanceof ArrayList) {
        return setExpr_adapter;
      }
      else if (code instanceof String) {
        return refExpr_adapter;
      }
      else if (code == null) {
        throw new AdapterException("Null Expr ");
      }
      else {
        throw new AdapterException("Unsupported Expr "
            + code.getClass().toString());
      }
    } catch (AdapterException adapter_ex) {
      adapter_ex.printStackTrace();
      return null;
    }
  }
  
  /**
   * @param expr
   * @return
   */
  public static JComponent createJComponentForExpr(Expr expr)
  {
    try {
      if (expr instanceof BindExpr) {
        return new JTable();
      }
      else if (expr instanceof SetExpr) {
        return new JList();
      }
      else if (expr instanceof PowerExpr) {
        return new JList();
      }
      else if (expr instanceof RefExpr) {
        return new JTextField();
      }
      else if (expr instanceof GivenValue) {
        return new JTextField();
      }
      else if (expr == null) {
        throw new AdapterException("Null Expr ");
      }
      else {
        System.out.println(expr.toString());
        throw new AdapterException("Unsupported Expr " + expr.toString());
      }
    } catch (AdapterException adapter_ex) {
      adapter_ex.printStackTrace();
      return null;
    }
  }

  public static HashMap<String, Expr> prime(HashMap<String, Expr> target)
  {
    HashMap<String, Expr> result = new HashMap<String, Expr>();
    Expr expr;
    for (String key : target.keySet()) {
      expr = target.get(key);
      result.put(key + "'", expr);
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
      JComponent component = origin.get(key);
      if (component == null) {
        component = GaffeFactory.createJComponentForExpr(expr);
      }
      adapter = GaffeFactory.getAdapter(component);
      origin.put(key, adapter.dataToComponent(component, expr));
    }
    return origin;
  }
  
  public static Object encodeExpr(Expr expr){
    Adapter adapter = getAdapter(expr);
    return adapter.encodeExpr(expr);
  }
  
  public static Expr decodeExpr(Object code){
    Adapter adapter = getAdapter(code);
    return adapter.decodeExpr(code);
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
}
