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

package net.sourceforge.czt.jdsl.graph.api;

import net.sourceforge.czt.jdsl.core.api.*;



/**
 * An interface describing the modifier methods of a combinatorial
 * graph that can safely be inherited by more restricted graphs.
 *
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 * @see InspectableGraph
 */
public interface ModifiableGraph extends InspectableGraph,
    PositionalContainer {


  /**
   * Splits an existing edge by inserting a new vertex and two new edges,
   * and removing the old edge.
   * If the edge is directed, the two new edges maintain the
   * direction.  The old edge is removed; its <code>element()</code>
   * can still be retrieved.  The new edges store null elements, and the new
   * vertex stores the specified element.
   * @param e the edge to be split
   * @param vertElement the object to be stored in <code>v</code>
   * @return the new vertex <code>w</code>; to get the new edges, use method
   * <code>incidentEdges(w)</code>
   * @exception InvalidAccessorException if the edge does not belong
   * to this graph
   */
  public Vertex splitEdge (Edge e, Object vertElement) throws
  InvalidAccessorException;  

  /**
   * Transforms edge-vertex-edge into a single edge.  The vertex must
   * be of degree 2.  The edges and the vertex are removed (their
   * <code>element()s</code> can still be retrieved), and a new edge is 
   * inserted in their place.  The new edge stores the specified element.
   * <p>
   * If the two incident edges of <code>v</code>
   * are consistently directed, the new edge is directed in that
   * direction.  If they are both undirected, the new edge
   * is undirected.  Any other combination of directions also results in
   * an undirected edge.
   * 
   * @param v the vertex to be removed
   * @param edgeElement the element to be stored in the new edge
   * @exception InvalidVertexException If the vertex is not of degree 2
   * or is of degree 2 but the "two" edges are a single self-loop
   * @exception InvalidAccessorException if the vertex does not
   * belong to this graph
   * @return the new edge
   */
  public Edge unsplitEdge (Vertex v, Object edgeElement) throws
  InvalidAccessorException, InvalidVertexException;


  /* direction update methods */

  /**
   * Sets the direction of an edge away from a vertex.  Makes an
   * undirected edge directed.
   *
   * @param e an edge
   * @param v an endvertex of <code>e</code>
   * @exception InvalidVertexException if <code>v</code> is not an
   * endvertex of <code>e</code> but both <code>v</code> and
   * <code>e</code> belong to this graph
   * @exception InvalidAccessorException if either <code>e</code> or
   * <code>v</code> does not belong to this graph
   */
  public void setDirectionFrom (Edge e, Vertex v) throws
  InvalidAccessorException, InvalidVertexException;

  /**
   * Sets the direction of an edge towards a vertex.  Makes an
   * undirected edge directed.
   *
   * @param e an edge
   * @param v an endvertex of <code>e</code>
   * @exception InvalidVertexException if <code>v</code> is not an
   * endvertex of <code>e</code> 
   * @exception InvalidAccessorException if either <code>e</code> or
   * <code>v</code> does not belong to this graph
   */
  public void setDirectionTo (Edge e, Vertex v) throws
  InvalidAccessorException, InvalidVertexException;

  /**
   * Makes a directed edge undirected. Does nothing if the edge is
   * undirected.
   * @param e an edge
   * @exception InvalidAccessorException if the edge does not belong
   * to this graph
   */
  public void makeUndirected (Edge e) throws InvalidAccessorException;

  /**
   * Reverse the direction of an edge.
   * @param e an edge
   * @exception InvalidEdgeException If the edge is undirected
   * @exception InvalidAccessorException if the edge does not belong
   * to this graph
   */
  public void reverseDirection (Edge e) throws InvalidEdgeException,
      InvalidAccessorException;

}
