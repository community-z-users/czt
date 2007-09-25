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
import net.sourceforge.czt.jdsl.graph.api.VertexIterator;
import net.sourceforge.czt.modeljunit.Transition;

/** Counts the number of times each state has been entered.
 *  Each reset will increment the count of the initial state.
 *  Each transition will increment the count of its target state.
 *  <p>
 *  The getCoverage method will return the total number of states
 *  visited since the last clear.  The getMaximum method will
 *  return the total number of states in the graph, if this is known.
 *  </p>
 */
public class StateCoverage extends AbstractCoverage
{
  protected boolean todoReset_ = false;
  
  public String getName()
  {
    return "state coverage";
  }

  public String getDescription()
  {
    return "The number of different FSM states visited.";
  }

  @Override
  public void setGraph(InspectableGraph model, Map<Object, Vertex> state2vertex)
  {
    for (VertexIterator iter = model.vertices(); iter.hasNext();) {
      Vertex v = iter.nextVertex();
      addItem(v.element()); // get the FSM state object.
    }
    maxCoverage_ = coverage_.size();
  }

  @Override
  public void clear()
  {
    super.clear();
    todoReset_ = false;
  }

  /** Increments the count of the initial state.
   *  However, this is done just once for each sequence of resets.
   */
  @Override
  public void doneReset(String reason, boolean testing)
  {
    super.doneReset(reason, testing);
    todoReset_ = true;
  }

  /** Increments the count of the target state of the transition. */
  @Override
  public void doneTransition(int action, Transition tr)
  {
    super.doneTransition(action, tr);
    if (todoReset_) {
      todoReset_ = false;
      incrementItem(tr.getStartState());
    }
    incrementItem(tr.getEndState());
  }
}
