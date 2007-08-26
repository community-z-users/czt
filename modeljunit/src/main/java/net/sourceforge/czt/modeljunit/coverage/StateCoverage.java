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

import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.jdsl.graph.api.VertexIterator;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.Transition;

/** Measures the number of distinct Actions that have been tested.
 */
public class StateCoverage extends AbstractCoverage
{
  /** The current state of the FSM. */
  Object currState_ = null;

  public String getName()
  {
    return "State Coverage";
  }

  public String getDescription()
  {
    return "The number of different FSM states visited.";
  }

  @Override
  public void setModel(Graph model, Map<Object, Vertex> state2vertex)
  {
    for (VertexIterator iter = model.vertices(); iter.hasNext();) {
      Vertex v = iter.nextVertex();
      addItem(v.element()); // get the FSM state object.
    }
    maxCoverage_ = coverage_.size();
  }

  @Override
  public void doneTransition(int action, Transition tr)
  {
    Object oldState = tr.getStartState();
    if ( ! oldState.equals(currState_)) {
      // we have jumped somewhere, probably a reset.
      incrementItem(oldState);
    }
    currState_ = tr.getEndState();
    incrementItem(currState_);
  }
}
