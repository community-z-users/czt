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
 * An interface describing a combinatorial graph.  Directed and
 * undirected edges may coexist. Multiple parallel edges and
 * self-loops are allowed.  The graph can be disconnected.
 * 
 * Note that the <code>Vertex</code> and <code>Edge</code> interfaces,
 * which are subinterfaces of <code>net.sourceforge.czt.jdsl.core.api.Position</code>, are
 * empty interfaces, for type safety only.
 *
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 *
 * @see Vertex
 * @see Edge
 * @see ModifiableGraph
 */
public interface Graph extends ModifiableGraph {


  /**
   * Inserts a new isolated vertex.
   * @param element the object to be stored in the new vertex
   * @return the new vertex
   */
  public Vertex insertVertex (Object element);

  /**
   * Attaches a new vertex, containing an object, to an existing vertex
   * by inserting a new undirected edge.  This is equivalent to calling
   * <code>insertVertex(.)</code> followed by <code>insertEdge(.)</code>.
   * @param v a vertex
   * @param vertexElement the object to be stored in <code>v</code>
   * @param edgeElement the object to be stored in the new edge
   * @return the new edge e; to get the new vertex, use method
   * <code>opposite(v,e)</code>
   * @exception InvalidAccessorException if vertex to be attached to
   * does not belong to this graph
   */
  public Edge attachVertex (Vertex v, Object vertexElement,
			    Object edgeElement) throws InvalidAccessorException;

  /**
   * Attaches a new vertex, containing an object, by inserting a new
   * directed edge from an existing vertex.  This is equivalent to calling
   * <code>insertVertex(.)</code> followed by
   * <code>insertDirectedEdge(.)</code>. 
   * @param origin a vertex
   * @param vertexElement the object to be stored in <code>v</code>
   * @param edgeElement the object to be stored in the new edge
   * @return the new edge <code>e</code>; to get the new vertex, use method
   * <code>opposite(v,e)</code>
   * @exception InvalidAccessorException if <code>origin</code>
   * does not belong to this graph
   */
  public Edge attachVertexFrom (Vertex origin, Object vertexElement,
				Object edgeElement) throws
				InvalidAccessorException;

  /**
   * Attaches a new vertex, containing an object, by inserting a new
   * directed edge to an existing vertex.  This is equivalent to calling
   * <code>insertVertex(.)</code> followed by
   * <code>insertDirectedEdge(.)</code>.  
   * @param destination a vertex
   * @param vertexElement the object to be stored in <code>v</code>
   * @param edgeElement the object to be stored in the new edge
   * @return the new edge <code>e</code>; to get the new vertex, use method
   * <code>opposite(v,e)</code>
   * @exception InvalidAccessorException if <code>destination</code>
   * does not belong to this graph
   */
  public Edge attachVertexTo (Vertex destination, Object vertexElement,
			      Object edgeElement) throws InvalidAccessorException;

  /**
   * Inserts a new undirected edge between two existing vertices.
   * @param v1 the first endvertex
   * @param v2 the second endvertex
   * @param element the object to be stored in the new edge
   * @return the new edge
   * @exception InvalidAccessorException if either <code>v1</code> or
   * <code>v2</code> does not belong to this graph
   */
  public Edge insertEdge (Vertex v1, Vertex v2, Object element) throws
  InvalidAccessorException;

  /**
   * Inserts a new directed edge from an existing vertex to another.
   * @param v1 the origin vertex
   * @param v2 the destination vertex
   * @param element the object to be stored in the new edge
   * @return the new edge
   * @exception InvalidAccessorException if either <code>v1</code> or
   * <code>v2</code> does not belong to this graph
   */
  public Edge insertDirectedEdge (Vertex v1, Vertex v2, Object element) throws
  InvalidAccessorException;

  /**
   * Removes a vertex and all its incident edges.  If you need the
   * elements stored at the removed edges, get them beforehand.
   * @param v the vertex to be deleted
   * @return the element stored at <code>v</code>
   * @exception InvalidAccessorException if the vertex does not
   * belong to this graph
   */
  public Object removeVertex (Vertex v) throws InvalidAccessorException;
  
  /**
   * @param e the edge to be removed
   * @return the element formerly stored at <code>e</code>
   * @exception InvalidAccessorException if the edge does not belong
   * to this graph
   */
  public Object removeEdge (Edge e) throws InvalidAccessorException;

}
