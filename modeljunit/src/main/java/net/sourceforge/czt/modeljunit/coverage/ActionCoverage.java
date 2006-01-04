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

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.Transition;

/** Measures the number of distinct Actions that have been tested.
 */
public class ActionCoverage extends AbstractCoverage
{
  public ActionCoverage()
  {
    super();
  }

  public String getName()
  {
    return "Action Coverage";
  }

  public String getDescription()
  {
    return "The number of different actions executed.";
  }

  public void setModel(Graph model, Map<Object, Vertex> state2vertex)
  {
    for (EdgeIterator iter=model.edges(); iter.hasNext(); ) {
      Edge e = iter.nextEdge();
      addItem(e.element());
    }
    maxCoverage_ = coverage_.size();
  }

  public void doneTransition(Transition tr)
  {
    incrementItem(tr.getAction());
  }
}
