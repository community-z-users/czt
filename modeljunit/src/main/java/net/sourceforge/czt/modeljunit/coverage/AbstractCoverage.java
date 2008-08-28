/**
 Copyright (C) 2006 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit.coverage;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.AbstractListener;
import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.Transition;

/** A partial implementation of CoverageMetric.
 *  This maintains the map from Object to Integer,
 *  and calculates the coverage metrics from that.
 *  Note that currCoverage_ is the number of keys
 *  in the coverage_ map that have non-zero values.
 *  (The {@link #addItem(Object) addItem} and
 *  {@link #incrementItem(Object) incrementItem}
 *  methods maintain this invariant.)
 *  <p>
 *  Subclasses must implement the setGraph method so that
 *  it calls {@link #addItem(Object) addItem} for every item in
 *  the FSM graph.  After doing this,
 *  it should also set maxCoverage_ to coverage_.size().
 *  Subclasses must also implement doneTransition (and
 *  perhaps doneReset) so that it calls incrementCount(item)
 *  each time a coverage item is covered.  Of course, they
 *  must also implement <code>getName()</code> and
 *  <code>getDescription()</code> so that this metric has a
 *  meaningful name and some documentation.
 *  </p>
 */
public abstract class AbstractCoverage
  extends AbstractListener
  implements CoverageMetric
{
  /** Records the number of times each item has been covered.
   *  If possible, all changes to this field should be done
   *  via the methods {@link #clear() reset},
   *  {@link #addItem(Object) addItem} and
   *  {@link #incrementItem(Object) incrementItem},
   *  because they preserve the invariant that currCoverage_
   *  is the number of non-zero entries in the {@code coverage_} map.
   */
  protected/*@non_null@*/Map<Object, Integer> coverage_;

  /** The maximum number of coverage items.
   *  This is typically -1 (which means unknown) until setModel
   *  is called, then it is equal to the number of items in the
   *  {@code coverage_} map.
   */
  protected int maxCoverage_ = -1;

  /** The number of items that have been 'covered'.
   *  This is equal to the number of non-zero entries in {@code coverage_}.
   */
  protected int currCoverage_ = 0;

  /** This default constructor sets up the {@code coverage_} map,
   *  sets {@code maxCoverage=-1} (meaning unknown), and sets
   *  {@code currCoverage_=0}.
   */
  public AbstractCoverage()
  {
    maxCoverage_ = -1; // means maximum is unknown
    currCoverage_ = 0;
    coverage_ = new HashMap<Object, Integer>();
  }

  /** {@inheritDoc}
   *  <p>
   *  The default implementation iterates through the
   *  coverage_ map and resets all counts to zero, and also
   *  resets currCoverage_ to zero, to maintain the invariant.
   *  </p>
   */
  public void clear()
  {
    for (Object key : coverage_.keySet()) {
      coverage_.put(key, 0);
    }
    currCoverage_ = 0; // maintain the invariant.
  }

  /** Add a coverage item to the {@code coverage_} map.
   *  If the item is already in the map, its value is left
   *  unchanged.  If the item is new, its value is set to zero.
   *
   * @param item The object that is to be added to the coverage_ map.
   */
  protected void addItem(Object item)
  {
    if (!coverage_.containsKey(item))
      coverage_.put(item, 0);
  }

  /** Increments the count of {@code item} in the {@code coverage_} map.
   *  This should be called by {@link #doneTransition(int,Transition) doneTransition}
   *  (and perhaps doneReset) whenever a coverage item is covered.
   *  If item was not already in the map, then it is added to the map
   *  and its value is set to one.
   *
   * @param item The object that has just been 'covered'.
   */
  protected void incrementItem(Object item)
  {
    Integer result = coverage_.get(item);
    if (result == null) {
      result = 1;
      currCoverage_++; // it is a new (non-zero) entry.
    }
    else {
      if (result == 0)
        currCoverage_++; // it is changing from zero to non-zero.
      result++;
    }
    coverage_.put(item, result);
  }

  public int getCoverage()
  {
    return currCoverage_;
  }

  /** The maximum number of items that can be covered.
   *  For some coverage metrics, this may return -1 until the
   *  FSM graph is completely built.
   */
  public int getMaximum()
  {
    if (maxCoverage_ > 0 && maxCoverage_ < coverage_.size()) {
      maxCoverage_ = coverage_.size();
    }
    return maxCoverage_;
  }

  public float getPercentage()
  {
    return (100.0F * getCoverage()) / (float) getMaximum();
  }

  public Map<Object, Integer> getDetails()
  {
    return coverage_;
  }

  public String toString()
  {
    int max = getMaximum();
    if (max < 0) {
      return getCoverage() + "/???";
    }
    else {
      return getCoverage() + "/" + getMaximum();
    }
  }

  /** A convenience method for converting a graph edge into a Transition. */
  public static Transition transition(Edge e, InspectableGraph model)
  {
    Object origin = model.origin(e).element();
    Object dest = model.destination(e).element();
    String action = (String) e.element();
    return new Transition(origin, action, dest);
  }

  /** {@inheritDoc}
   *  <p>
   *  The default implementation does nothing.
   *  </p>
   */
  public void doneReset(String reason, boolean testing)
  {
  }

  /** A default implementation that does nothing. */  
  public void setGraph(InspectableGraph model, Map<Object, Vertex> state2vertex)
  {
  }
}
