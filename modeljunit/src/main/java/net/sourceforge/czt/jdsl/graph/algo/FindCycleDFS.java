/*
  Copyright (c) 1999, 2000 Brown University, Providence, RI
  
                            All Rights Reserved
  
  Permission to use, copy, modify, and distribute this software and its
  documentation for any purpose other than its incorporation into a
  commercial product is hereby granted without fee, provided that the
  above copyright notice appear in all copies and that both that
  copyright notice and this permission notice appear in supporting
  documentation, and that the name of Brown University not be used in
  advertising or publicity pertaining to distribution of the software
  without specific, written prior permission.
  
  BROWN UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
  SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR ANY PARTICULAR PURPOSE.  IN NO EVENT SHALL BROWN
  UNIVERSITY BE LIABLE FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL
  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
  PERFORMANCE OF THIS SOFTWARE.
*/

package net.sourceforge.czt.jdsl.graph.algo;

import net.sourceforge.czt.jdsl.graph.api.*;
import net.sourceforge.czt.jdsl.graph.ref.*;
import net.sourceforge.czt.jdsl.core.api.Sequence;
import net.sourceforge.czt.jdsl.core.api.ObjectIterator;
import net.sourceforge.czt.jdsl.core.ref.NodeSequence;


/**
 * This class specializes DFS to determine if the connected component
 * of the start vertex contains a cycle and if so return it. The
 * algorithm creates an ObjectIterator of vertices in the cycle or an
 * empty ObjectIterator if there is no cycle. The ObjectIterator is
 * accessed via the getCycle() method.
 *   
 * @author Natasha Gelfand
 * @author Keith Schmidt (kas)
 * @version JDSL 2.1.1 
 * @see DFS 
 */

public class FindCycleDFS extends DFS {

  /**
   * This stores a list of Vertices which are being checked to see if
   * there is a cycle among them.
   */
  protected Sequence prospectiveCycle_;

  /**
   * This is set to true if a cycle is found, alerting the DFS to
   * finish early
   */
  protected boolean done_;

  /**
   * The Vertex which has been encountered twice on one path, proving
   * that a cycle exists.
   */
  protected Vertex cycleStart_;

  /**
   * An Iterator over all of the Vertices in the found cycle.
   */  
  private ObjectIterator cycleIterator_;

  /**
   * Simple constructor initializes instance variables.
   */
  public FindCycleDFS() {
    prospectiveCycle_ = new NodeSequence();
    done_ = false;
  }

  public void execute(InspectableGraph g, Vertex start) {
    super.execute(g, start);

    // The path is a stack represented as a Sequence where items are
    // added and removed at the front. Therefore, if a cycle has been
    // found, the first element of the Sequence is the last Vertex
    // before the cycle closure. Hence we can iterate through the
    // Sequence, stepping back along the path until we find the Vertex
    // that closed the cycle.
    //
    // If no cycle is found, the Sequence will be empty and the cycle
    // Iterator will be empty
    Sequence theCycle = new NodeSequence();
    ObjectIterator pathVerts = prospectiveCycle_.elements();
    while (pathVerts.hasNext()) {
      Vertex v = (Vertex)pathVerts.nextObject();
      theCycle.insertFirst(v);
      if (v == cycleStart_) {
	break;
      }
    }
    // remove all decorations added during the DFS
    cleanup();
    // get ready to return the cycle.
    cycleIterator_ = theCycle.elements();
  }
    
  /**
   * As new vertices are visited, they are added to the prospective
   * cyclic path.
   */
  protected void startVisit(Vertex v) { 
    prospectiveCycle_.insertFirst(v); 
  }

  /**
   * Once the visit has ended, they are removed from the prospective
   * cyclic path.
   */
  protected void finishVisit(Vertex v) { 
    if (!done_) { 
      prospectiveCycle_.remove(prospectiveCycle_.first());
    }
  }

  /**
   * When a back edge has been encountered, the graph has a cycle.
   */
  protected void traverseBackEdge(Edge e, Vertex from) {
    cycleStart_ = graph_.opposite(from, e);
    done_ = true;
  }
  
  /**
   * Returns true iff a cycle has been found.
   */
  protected boolean isDone() { return done_; } 

  /**
   * Returns an ObjectIterator containing all of the Vertices in the
   * found cycle.
   */
  public ObjectIterator getCycle() {
    return cycleIterator_;
  }
  
  /**
   * This method tells the DFS which graph edges to check. This one
   * chooses all of them
   * @param v - the Vertex to which the edges must be incident.
   */
  protected EdgeIterator interestingIncidentEdges(Vertex v) 
    { return graph_.incidentEdges(v);}

}
