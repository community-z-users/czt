
package net.sourceforge.czt.animation.model;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.swing.tree.DefaultMutableTreeNode;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.view.OutputPane;
import net.sourceforge.czt.animation.view.StatePane;
import net.sourceforge.czt.animation.view.ToolBar;
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

  private List<HashMap<String, Object>> encodable;

  private EvalResult evalResult;

  private PropertyChangeSupport pcs;

  /**
   * 
   */
  public Step()
  {
    this("Empty", null);
  }

  /**
   * @param operation
   * @param evalResult
   */
  public Step(String operation, EvalResult evalResult)
  {
    this.index = -1;
    this.isComplete = false;
    this.operation = operation;
    this.encodable = new ArrayList<HashMap<String, Object>>();
    this.evalResult = evalResult;
    this.results = new ArrayList<HashMap<String, Expr>>();
    this.pcs = new PropertyChangeSupport(this);
    if (evalResult != null)
      this.changeIndex(0);
  }

  /**
   * @return Returns the index.
   */
  public int getIndex()
  {
    return index;
  }

  /**
   * @return Returns the operation.
   */
  public String getOperation()
  {
    return operation;
  }

  /**
   * @return Returns the encodable.
   */
  public List<HashMap<String, Object>> getEncodable()
  {
    return encodable;
  }

  /**
   * @param index The index to set.
   */
  public void setIndex(int newValue)
  {
    int oldValue = index;
    index = newValue;
    this.firePropertyChange("index", oldValue, newValue);
  }

  /**
   * @param isComplete The isComplete to set.
   */
  public void setComplete(boolean isComplete)
  {
    this.isComplete = isComplete;
  }

  /**
   * @param operation The operation to set.
   */
  public void setOperation(String operation)
  {
    this.operation = operation;
  }

  /**
   * @param encodable The encodable to set.
   */
  public void setEncodable(List<HashMap<String, Object>> encodable)
  {
    this.encodable = encodable;
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeSupport#addPropertyChangeListener(java.beans.PropertyChangeListener)
   */
  public void addPropertyChangeListener(PropertyChangeListener arg0)
  {
    pcs.addPropertyChangeListener(arg0);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeSupport#firePropertyChange(java.lang.String, int, int)
   */
  public void firePropertyChange(String arg0, int arg1, int arg2)
  {
    pcs.firePropertyChange(arg0, arg1, arg2);
  }

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

  /**
   * @return size
   */
  public int size()
  {
    return results.size();
  }

  /**
   * @return Returns the isComplete.
   */
  public boolean isComplete()
  {
    return isComplete;
  }

  /**
   * @return The selected Result
   */
  public HashMap<String, Expr> getResultSelected()
  {
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
   * @param index The index to set.
   */
  public boolean changeIndex(int newValue)
  {
    if (newValue < 0 || evalResult == null) {
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
          newMap.put(key, GaffeFactory.encodeExpr(expr));
        }
        encodable.add(newMap);
      }
    }
    isComplete = !evalResult.hasNext();
    this.setIndex(newValue);
    return true;
  }

  public void restore()
  {
    HashMap<String, Expr> result;
    for (HashMap<String, Object> encodedMap : encodable) {
      result = new HashMap<String, Expr>();
      for (String key : encodedMap.keySet()) {
        Object code = encodedMap.get(key);
        Expr expr = GaffeFactory.decodeExpr(code);
        result.put(key, expr);
      }
      results.add(result);
    }
    this.pcs = new PropertyChangeSupport(this);
    this.addPropertyChangeListener(StatePane.getCurrentPane());
    this.addPropertyChangeListener(OutputPane.getCurrentPane());
    this.addPropertyChangeListener(ToolBar.getCurrentToolBar());
  }
}
