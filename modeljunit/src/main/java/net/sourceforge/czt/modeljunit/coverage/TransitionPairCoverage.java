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

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeDirection;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.jdsl.graph.api.VertexIterator;
import net.sourceforge.czt.modeljunit.Transition;
import net.sourceforge.czt.modeljunit.TransitionPair;

/** Measures the number of distinct Actions that have been tested.
 */
public class TransitionPairCoverage extends AbstractCoverage
{
  /** The current state of the FSM. */
  Transition lastTransition_ = null;

  public String getName()
  {
    return "transition-pair coverage";
  }

  public String getDescription()
  {
    return "All the pairs of transitions (t1,t2), where t1 is a transition"
      +" that leads into some state and t2 is a transition that leads"
      +" out of that same state.";
  }

  @Override
  public void setGraph(InspectableGraph model, Map<Object, Vertex> state2vertex)
  {
    for (VertexIterator iter=model.vertices(); iter.hasNext(); ) {
      Vertex v = iter.nextVertex();
      for (EdgeIterator incoming = model.incidentEdges(v,EdgeDirection.IN);
           incoming.hasNext(); ) {
        Edge in = incoming.nextEdge();
        Transition inTrans = transition(in, model);
        for (EdgeIterator outgoing = model.incidentEdges(v,EdgeDirection.OUT);
             outgoing.hasNext(); ) {
          Edge out = outgoing.nextEdge();
          Transition outTrans = transition(out, model);
          TransitionPair pair = new TransitionPair(inTrans,outTrans);
          addItem(pair);
        }
      }
    }
    maxCoverage_ = coverage_.size();
  }

  @Override
  public void doneReset(String reason, boolean testing)
  {
    lastTransition_ = null;
  }

  @Override
  public void doneTransition(int action, Transition tr)
  {
    if (lastTransition_ != null
        && lastTransition_.getEndState().equals(tr.getStartState())) {
      TransitionPair pair = new TransitionPair(lastTransition_, tr);
      incrementItem(pair);
    }
    lastTransition_ = tr;
  }
}
