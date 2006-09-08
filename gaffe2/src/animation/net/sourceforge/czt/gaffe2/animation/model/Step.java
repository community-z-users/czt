
package net.sourceforge.czt.gaffe2.animation.model;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.swing.tree.DefaultMutableTreeNode;

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
  
  private List<HashMap<String, String>> encodable;

  private EvalResult evalResult;
  
  private PropertyChangeSupport pcs;

  /**
   * 
   */
  public Step()
  {
    this("Empty",null);
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
    this.encodable = new ArrayList<HashMap<String, String>>();
    this.evalResult = evalResult;
    this.results = new ArrayList<HashMap<String, Expr>>();
    this.pcs = new PropertyChangeSupport(this);
    if (evalResult!=null) this.changeIndex(0);
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
  public List<HashMap<String, String>> getEncodable()
  {
    return encodable;
  }
  
  /**
   * @param index The index to set.
   */
  public void setIndex(int index)
  {
    this.index = index;
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
  public void setEncodable(List<HashMap<String, String>> encodable)
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
  public String toString(){
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
    int oldValue = index;
    if (newValue < 0 || evalResult==null) {
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
        HashMap<String, String> newMap = new HashMap<String, String>();
        for (String key : result.keySet()){
          newMap.put(key, result.get(key).toString());
        }
        encodable.add(newMap);
      }
    }
    index = newValue;
    isComplete = !evalResult.hasNext();
    this.firePropertyChange("index", oldValue, newValue);
    return true;
  }
}
