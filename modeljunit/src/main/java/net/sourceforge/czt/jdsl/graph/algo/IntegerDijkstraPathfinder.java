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

import net.sourceforge.czt.jdsl.core.api.*;
import net.sourceforge.czt.jdsl.core.ref.NodeSequence;
import net.sourceforge.czt.jdsl.graph.api.*;
import net.sourceforge.czt.jdsl.graph.ref.EdgeIteratorAdapter;



/**
 * using Dijkstra's algorithm.  You must extend this class and
 * implement the weight(Edge) method.  As always, Dijkstra's algorithm
 * cannot handle negative-weight edges.  <p>
 *
 * If necessary, you also have access to all the customization methods
 * of IntegerDijkstraTemplate, although using some of them without the
 * knowledge of this class could give incorrect results.  <p>
 *   
 * @version JDSL 2.1.1 
 * @author Mark Handy
 * @author Luca Vismara
 */
public abstract class IntegerDijkstraPathfinder
  extends IntegerDijkstraTemplate {

  // instance variables

  private Vertex dest_;


  // overridden instance methods from IntegerDijkstraTemplate

  protected boolean shouldContinue () {
    return !isFinished(dest_);
  }

  
  // instance methods

  /** 
   * Returns whether a path between the source and the destination exists
   *
   * @return whether there is a path from source to destination
   */
  public boolean pathExists () {
    return isReachable(dest_);
  }
  
  /** 
   * @return Iterator over the edges, in order, of a shortest path
   * from source to destination
   */
  public EdgeIterator reportPath () throws InvalidQueryException {
    if (!pathExists())
      throw new InvalidQueryException("No path exists between "+source_
				      +" and "+dest_);
    else {
      Sequence retval = new NodeSequence();
      Vertex currVertex = dest_;
      while (currVertex != source_) {
	assert isFinished(currVertex);
	Edge currEdge = getEdgeToParent(currVertex);
	assert currEdge != null;
	retval.insertFirst(currEdge);
	currVertex = g_.opposite(currVertex,currEdge);
      }
      return new EdgeIteratorAdapter(retval.elements());
    }
  }

  /** 
   * @param g the graph on which to execute the algorithm
   * @param source the source vertex
   * @param dest the destination vertex
   * @exception InvalidVertexException if source or dest are not
   * contained in g
   */
  public final void execute (InspectableGraph g, Vertex source, Vertex dest)
    throws InvalidVertexException {
    if (!g.contains(source))
      throw new InvalidVertexException(source+" not contained in "+g);
    else if (!g.contains(dest))
      throw new InvalidVertexException(dest+" not contained in "+g);
    else {
      dest_ = dest;
      init(g,source);
      if (source_ != dest_)
	runUntil();
    }
  }

}
