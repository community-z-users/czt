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

import java.util.Map;

import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.ModelListener;

/** An interface to a test coverage metric.
 */
public interface CoverageMetric extends ModelListener
{
  /** A medium-length description of this coverage metric.
   *  This should be a sentence or paragraph suitable for 
   *  displaying as pop-up documentation, to explain the metric.
   *  For example, a state coverage metric might return
   *  "The number of different FSM states visited.".
   */
  public /*@non_null@*/ String getDescription();

  /** Reset all coverage data.
   *  After calling this method, getCoverage() will return 0.
   *  Resetting the coverage does not imply that the model has changed,
   *  so the result of getMaximum() should be unchanged.
   */
  public void clear();

  /** The number of 'items' covered so far.
   *  The definition of 'item' depends upon the kind of coverage
   *  that is being counted.  For example, it could be states,
   *  or actions, or transitions, or transition-pairs, or steps,
   *  or test sequences etc. */ 
  public int getCoverage();

  /** The maximum coverage possible.
   *  This is useful for calculating the percentage of coverage.
   *  Note that a few coverage metrics (like the number of tests,
   *  or the total length of the test sequences) have no maximum,
   *  so in this case, getMaximum() returns -1.
   *  Similarly, getMaximum() may return -1 until the
   *  the graph has been fully explored.
   */ 
  public int getMaximum();

  /** The current coverage percentage.
   *  This is equivalent to (100.0 * getCoverage()) / getMaximum().
   *  So the result will be a large negative number
   *  before setModel is called, or for coverage metrics that
   *  have no maximum coverage.
   */ 
  public float getPercentage();

  /** Details of which items have been covered and how many times.
   *  Coverage metrics that cannot provide this level of detail will
   *  return null.
   *  <p> 
   *  The type of objects in the domain of the result map will depend
   *  upon the kind of coverage (Action, Transition, TransitionPair etc.).
   *  However, all of them should provide a useful toString() method,
   *  so that you can print coverage results.  A typical use of this
   *  method is to iterate through the result map and print all the
   *  objects that map to zero, because they have not been covered.
   *  </p>
   *  @return  Map of how many times each object has been covered, or null.
   */
  public Map<Object,Integer> getDetails();
  
  /** This is called when the graph seems to be complete.
   * @param model
   * @param state2vertex
   */
  public void setGraph(InspectableGraph model, Map<Object, Vertex> state2vertex);
}
