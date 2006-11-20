
package net.sourceforge.czt.animation.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.swing.tree.DefaultMutableTreeNode;

import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class Step extends DefaultMutableTreeNode
{
  private int index;

  private boolean isComplete;

  private String operation;

  private List<HashMap<String, Expr>> results;

  private List<HashMap<String, Object>> mirror;

  private EvalResult evalResult;

  /**
   * Empty Constructor
   */
  public Step()
  {
    this("Empty", null);
  }

  /**
   * @param operation
   * @param evalResult
   */
  public Step(String oper, EvalResult result)
  {
    index = -1;
    isComplete = false;
    operation = oper;
    mirror = new ArrayList<HashMap<String, Object>>();
    evalResult = result;
    results = new ArrayList<HashMap<String, Expr>>();
    if (evalResult != null) {
      this.changeIndex(0);
    }
    else {
      this.isComplete = true;
    }
  }

  /**
   * @return size
   */
  public int size()
  {
    return results.size();
  }

  /**
   * @param index The index to set.
   */
  public boolean changeIndex(int newValue)
  {
    if (newValue < 0) {
      return false;
    }
    while (newValue >= results.size()) {
      HashMap<String, Expr> result = evalResult.next();
      if (result == null) {
        isComplete = true;
        return false;
      }
      else {
        results.add(result);
        HashMap<String, Object> newMap = new HashMap<String, Object>();
        for (String key : result.keySet()) {
          Expr expr = result.get(key);
          newMap.put(key, GaffeUtil.encodeExpr(expr));
        }
        mirror.add(newMap);
      }
    }
    isComplete = !evalResult.hasNext();
    setIndex(newValue);
    return true;
  }

  /**
   * @return The selected Result
   */
  public HashMap<String, Expr> getResultSelected()
  {
    if (index == -1)
      return null;
    return results.get(index);
  }

  /**
   * @param i
   * @return indexed result
   */
  public HashMap<String, Expr> getResultByIndex(int i)
  {
    assert (i < results.size());
    return results.get(i);
  }

  /**
   * restore the mirror to expr map
   */
  public void restore()
  {
    HashMap<String, Expr> result;
    for (HashMap<String, Object> encodedMap : mirror) {
      result = new HashMap<String, Expr>();
      for (String key : encodedMap.keySet()) {
        Object code = encodedMap.get(key);
        Expr expr = GaffeUtil.decodeExpr(code);
        result.put(key, expr);
      }
      results.add(result);
    }
  }

  /*--------------------------------------------------------------------------*/
  // Getter and Setters
  /**
   * @return Returns the index.
   */
  public int getIndex()
  {
    return index;
  }

  /**
   * @param index
   */
  public void setIndex(int index)
  {
    this.index = index;
  }

  /**
   * @return Returns the isComplete.
   */
  public boolean isComplete()
  {
    return isComplete;
  }

  /**
   * @param isComplete The isComplete to set.
   */
  public void setComplete(boolean isComplete)
  {
    this.isComplete = isComplete;
  }

  /**
   * @return Returns the operation.
   */
  public String getOperation()
  {
    return operation;
  }

  /**
   * @param operation The operation to set.
   */
  public void setOperation(String operation)
  {
    this.operation = operation;
  }

  /**
   * @return Returns the mirror.
   */
  public List<HashMap<String, Object>> getMirror()
  {
    return mirror;
  }

  /**
   * @param mirror The mirror to set.
   */
  public void setMirror(List<HashMap<String, Object>> mirror)
  {
    this.mirror = mirror;
  }

  /*--------------------------------------------------------------------------*/

  /* (non-Javadoc)
   * @see java.lang.Object#toString()
   */
  public String toString()
  {
    return operation;
  }

  /**
   * For debug
   */
  public void print()
  {
    HashMap<String, Expr> result = this.getResultSelected();
    for (String key : result.keySet()) {
      System.out.println(key + ": " + result.get(key).toString());
    }
  }
}
