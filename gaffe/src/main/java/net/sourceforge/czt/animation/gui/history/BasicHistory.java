/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.history;

import java.util.List;
import java.util.ListIterator;
import java.util.Vector;

import net.sourceforge.czt.animation.gui.temp.SolutionSet;

/**
 * Basic History Interface that provides the traditional back/forward mechanism.
 */
public class BasicHistory extends HistorySupport
{
  //Members
  /**
   * The list of solution sets.
   */
  protected List<SolutionSet> solutionSets;

  /**
   * The iterator identifying the current solution set.
   * Because <code>ListIterator</code>s identify a point between elements, and
   * not a current element:
   * the current solution is considered to be the one that would be returned by
   * <code>currentSolution.next()</code>.
   * This leads to a lot of extra fluffing around, so any code subclassing
   * BasicHistory would do better to go through the public functions
   * <code>BasicHistory</code> provides.
   */
  protected ListIterator<SolutionSet> currentSolution;

  //Constructors
  /**
   * Basic constructor, initialises the list of solution sets to empty.
   * An initialisation schema must be set before the history can be used.
   * @see History#activateSchema(String)
   */
  public BasicHistory()
  {
    super();
    solutionSets = new Vector<SolutionSet>();
    currentSolution = solutionSets.listIterator();
  };

  public BasicHistory(String stateSchema, String initSchema)
  {
    super(stateSchema, initSchema);
    solutionSets = new Vector<SolutionSet>();
    currentSolution = solutionSets.listIterator();
  };

  //Functions from History
  public synchronized SolutionSet getCurrentSolutionSet()
  {
    if (!currentSolution.hasNext())
      return null;
    SolutionSet current = (SolutionSet) currentSolution.next();
    currentSolution.previous();
    return current;
  };

  public synchronized void activateSchema(String schemaName)
  {
    super.activateSchema(schemaName); //XXX does nothing at the moment
  };

  //Methods for navigating through the solution sets.
  /**
   * @return true if there is another solution set after the current one.
   */
  public synchronized boolean hasNextSolutionSet()
  {
    if (!currentSolution.hasNext())
      return false;
    currentSolution.next();
    boolean result = currentSolution.hasNext();
    currentSolution.previous();
    return result;
  }

  /**
   * Moves to the next solution set.
   */
  public synchronized void nextSolutionSet()
  {
    if (hasNextSolutionSet()) {
      currentSolution.next();
      propertyChangeSupport
          .firePropertyChange("currentSolutionSet", null, null);
      propertyChangeSupport.firePropertyChange("currentSolution", null, null);
    }
  };

  /**
   * @return true if there is another solution set before the current one.
   */
  public synchronized boolean hasPreviousSolutionSet()
  {
    return currentSolution.hasPrevious();
  };

  /**
   * Moves to the previous solution set.
   */
  public synchronized void previousSolutionSet()
  {
    if (hasPreviousSolutionSet()) {
      currentSolution.previous();
      propertyChangeSupport
          .firePropertyChange("currentSolutionSet", null, null);
      propertyChangeSupport.firePropertyChange("currentSolution", null, null);
    }
  };

  public String getPositionLabel()
  {
    if (solutionSets.size() == 0)
      return "0/0";
    else
      return "" + (currentSolution.nextIndex() + 1) + "/" + solutionSets.size();
  };
};
