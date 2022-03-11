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

package net.sourceforge.czt.animation.gui.temp;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.HashSet;
import java.util.ListIterator;
import java.util.Set;

/**
 * Class representing the set of solutions produced by an operation.
 */
public class SolutionSet
{
  protected final PropertyChangeSupport propertyChangeSupport_ = new PropertyChangeSupport(
      this);

  private ZSet solutions_;

  private ListIterator<ZValue> currentSolution_;

  private String schemaName_;

  /**
   * Creates a <code>SolutionSet</code> from a <code>Set</code> containing all
   * of the solutions.
   * @param schemaName The name of the schema that created this solution set.
   * @param solutions The set of solutions to go into this
   *        <code>SolutionSet</code>.
   */
  public SolutionSet(String schemaName, Set<? extends ZValue> solutions)
  {
    schemaName_ = schemaName;
    solutions_ = new ZSet(solutions);
    currentSolution_ = solutions_.iterator();
  }

  /**
   * Creates a <code>SolutionSet</code> containing just one solution.
   * @param schemaName The name of the schema that created this solution set.
   * @param solution The solution to go into this singleton
   *        <code>SolutionSet</code>.
   */
  public SolutionSet(String schemaName, ZBinding solution)
  {
    schemaName_ = schemaName;
    HashSet<ZBinding> tempSet = new HashSet<ZBinding>();
    tempSet.add(solution);
    solutions_ = new ZSet(tempSet);
    currentSolution_ = solutions_.iterator();
  }

  /**
   * Getter function for the name of the schema that created this solution set.
   * @return The name of the schema.
   */
  public String getSchemaName()
  {
    return schemaName_;
  }

  /**
   * Getter function for the currently selected solution in the SolutionSet.
   * @return The solution (or <code>null</code> if there is no current
   *         solution).
   */
  public ZBinding getCurrentSolution()
  {
    if (!currentSolution_.hasNext())
      return null;
    ZBinding current = (ZBinding) currentSolution_.next();
    currentSolution_.previous();
    return current;
  }

  /**
   * @return <code>true</code> if there is a current solution (i.e. if
   *         {@link #getCurrentSolution} <em>will not</em> return
   *         <code>null</code>).
   */
  public boolean hasCurrentSolution()
  {
    return currentSolution_.hasNext();
  }

  /**
   * @return <code>true</code> if there is a next solution in the
   *         <code>SolutionSet</code> (similar to hasNext in
   *         <code>Iterator</code>s).
   */
  public boolean hasNextSolution()
  {
    if (!hasCurrentSolution())
      return false;
    currentSolution_.next();
    boolean hasnext = currentSolution_.hasNext();
    currentSolution_.previous();
    return hasnext;
  }

  /**
   * Steps the current solution to the next in this <code>SolutionSet</code>.
   * Does nothing if it is already at the first solution.
   */
  public void nextSolution()
  {
    if (hasNextSolution()) {
      currentSolution_.next();
      propertyChangeSupport_.firePropertyChange("currentSolution", null, null);
    }
  }

  /**
   * @return <code>true</code> if there is a previous solution in the
   *         <code>SolutionSet</code> (similar to hasPrevious in
   *         <code>Iterator</code>s).
   */
  public boolean hasPreviousSolution()
  {
    return currentSolution_.hasPrevious();
  }

  /**
   * Steps the current solution to the previous in this
   * <code>SolutionSet</code>.
   * Does nothing if it is already at the last solution.
   */
  public void previousSolution()
  {
    if (hasPreviousSolution()) {
      currentSolution_.previous();
      propertyChangeSupport_.firePropertyChange("currentSolution", null, null);
    }
  }

  /**
   * Registers a <code>PropertyChangeListener</code>.
   * The only property that will trigger a <code>PropertyChangeEvent</code> is
   * {@link #currentSolution_ currentSolution}.
   */
  public void addPropertyChangeListener(PropertyChangeListener listener)
  {
    propertyChangeSupport_.addPropertyChangeListener(listener);
  }

  /**
   * Unregisters a <code>PropertyChangeListener</code>.
   * The only property that will trigger a <code>PropertyChangeEvent</code> is
   * {@link #currentSolution_ currentSolution}.
   */
  public void removePropertyChangeListener(PropertyChangeListener listener)
  {
    propertyChangeSupport_.addPropertyChangeListener(listener);
  }

  /**
   * Returns all of the <code>PropertyChangeListener</code>s.
   * The only property that will trigger a <code>PropertyChangeEvent</code> is
   * {@link #currentSolution_ currentSolution}.
   */
  public PropertyChangeListener[] getPropertyChangeListeners()
  {
    return propertyChangeSupport_.getPropertyChangeListeners();
  }

  /**
   * Registers a <code>PropertyChangeListener</code> for a specific property.
   * The only property that will trigger a <code>PropertyChangeEvent</code> is
   * {@link #currentSolution_ currentSolution}.
   */
  public void addPropertyChangeListener(String propertyName,
      PropertyChangeListener listener)
  {
    propertyChangeSupport_.addPropertyChangeListener(propertyName, listener);
  }

  /**
   * Unregisters a <code>PropertyChangeListener</code> for a specific property.
   * The only property that will trigger a <code>PropertyChangeEvent</code> is
   * {@link #currentSolution_ currentSolution}.
   */
  public void removePropertyChangeListener(String propertyName,
      PropertyChangeListener listener)
  {
    propertyChangeSupport_.removePropertyChangeListener(propertyName, listener);
  }

  /**
   * Returns all of the <code>PropertyChangeListener</code>s for a specific
   * property.
   * The only property that will trigger a <code>PropertyChangeEvent</code> is
   * {@link #currentSolution_ currentSolution}.
   */
  public PropertyChangeListener[] getPropertyChangeListeners(String propertyName)
  {
    return propertyChangeSupport_.getPropertyChangeListeners(propertyName);
  }

  /**
   * @return <code>true</code> if there are no
   *         <code>PropertyChangeListener</code>s registered.
   public boolean hasListeners(String propertyName)
   {
   return propertyChangeSupport_.hasListeners(propertyName);
   };
   /**
   * @return A <code>String</code> suitable for displaying to users to identify
   *         the current place in the <code>SolutionSet</code>.
   */
  public String getPositionLabel()
  {
    if (solutions_.size() == 0)
      return "0/0";
    return "" + (currentSolution_.nextIndex() + 1) + "/" + solutions_.size();
  }
}
