package czt.animation.gui.history;
import czt.animation.gui.temp.*;
import java.util.List;
import java.util.ListIterator;
import java.util.Vector;
import java.beans.*;


/**
 * Basic History Interface that provides the traditional back/forward mechanism.
 */
public class BasicHistory extends HistorySupport {
  
  //Members
  /**
   * The list of solution sets.
   */
  protected List solutionSets;
  /**
   * The iterator identifying the current solution.
   * Because <code>ListIterator</code>s identify a point between elements, and not a current element: 
   * the current solution is considered to be the one that would be returned by 
   * <code>currentSolution.next()</code>.
   * This leads to a lot of extra fluffing around, so any code subclassing BasicHistory would do 
   * better to go through the public functions BasicHistory provides.
   */
  protected ListIterator currentSolution;

  //Constructors
  /**
   * Basic constructor, initialises the list of solution sets to empty.
   * An initialisation schema must be set before the history can be used.
   * @see czt.animation.gui.history.History#activateSchema(String)
   */
  public BasicHistory() {
    super();
    solutionSets=new Vector();
    currentSolution=solutionSets.listIterator();
  };


  //Functions from History
  public synchronized SolutionSet getCurrentSolutionSet() {
    if(!currentSolution.hasNext()) return null;
    SolutionSet current=(SolutionSet)currentSolution.next();
    currentSolution.previous();
    return current;
  };
  public synchronized void activateSchema(String schemaName) {
    super.activateSchema(schemaName);//XXX does nothing at the moment
  };


  //Methods for navigating through the solution sets.
  /**
   * @return true if there is another solution set after the current one.
   */
  public synchronized boolean hasNextSolutionSet() {
    if(!currentSolution.hasNext()) return false;
    currentSolution.next();
    boolean result=currentSolution.hasNext();
    currentSolution.previous();
    return result;
  }
  /**
   * Moves to the next solution set
   */
  public synchronized void nextSolutionSet() {
    if(hasNextSolutionSet()) {
      currentSolution.next();
      propertyChangeSupport.firePropertyChange("currentSolutionSet",null,null);
      propertyChangeSupport.firePropertyChange("currentSolution",null,null);
    }
  };
  /**
   * @return true if there is another solution set before the current one.
   */
  public synchronized boolean hasPreviousSolutionSet() {
    return currentSolution.hasPrevious();
  };
  /**
   * Moves to the previous solution set
   */
  public synchronized void previousSolutionSet() {
    if(hasPreviousSolutionSet()) {
      currentSolution.previous();
      propertyChangeSupport.firePropertyChange("currentSolutionSet",null,null);
      propertyChangeSupport.firePropertyChange("currentSolution",null,null);
    }
  };
};

