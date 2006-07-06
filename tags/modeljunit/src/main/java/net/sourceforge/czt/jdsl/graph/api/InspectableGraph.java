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
 * An interface describing the accessor methods of a combinatorial
 * graph.  Holds both directed and undirected edges, and self-loops
 * and parallel edges.  An undirected edge is not the same as a pair
 * of undirected edges. The graph can be disconnected.  Subinterfaces 
 * can restrict any of these properties.
 * <p>
 * All iterators returned from graphs have snapshot semantics.  That is,
 * their contents are fixed at the moment the iterator is returned and
 * remain unchanged even if the container is changed before the
 * iterator has been exhausted.
 * <p>
 * No order is
 * guaranteed on the vertices or edges of the graph (the sets of vertices
 * and edges are just that:  unordered sets).  
 * <p>
 * Some methods dealing with edge directions take a constant, or an
 * OR of constants, from the <code>EdgeDirection</code>
 * interface.  For instance,<br> 
 * <code>incidentEdges(v)</code> gets all edges incident on <code>v</code>,<br>
 * <code>incidentEdges(v, EdgeDirection.IN)</code> gets all edges
 * directed toward <code>v</code>, and<br> 
 * <code>incidentEdges(v, EdgeDirection.IN | EdgeDirection.OUT)</code>
 * gets all directed edges incident on <code>v</code>.  
 *
 * @see ModifiableGraph
 * @see EdgeDirection
 * @author Luca Vismara (lv)
 * @author Mark Handy
 * @version JDSL 2.1.1 
 */
public interface InspectableGraph extends InspectablePositionalContainer {

  
  /* graph methods */

  /**
   * @return the number of vertices
   */
  public int numVertices();

  /**
   * @return the number of edges
   */
  public int numEdges();

  /**
   * @return an iterator over all vertices in the graph
   */
  public VertexIterator vertices();

  /**
   * @return an arbitrary vertex, or Vertex.NONE if the graph is empty
   */
  public Vertex aVertex();

  /**
   * @return an iterator over all edges in the graph
   */
  public EdgeIterator edges();

  /**
   * @return an arbitrary edge, or Edge.NONE if the graph has no edges
   */
  public Edge anEdge();

  /**
   * @return an iterator over all directed edges in the graph
   */
  public EdgeIterator directedEdges();

  /**
   * @return an iterator over all undirected edges in the graph
   */
  public EdgeIterator undirectedEdges();

  /**
   * @param v1 a vertex
   * @param v2 a vertex
   * @return whether <code>v1</code> and <code>v2</code> are adjacent,
   * i.e., whether they are 
   * the endvertices of a common edge
   * @exception InvalidAccessorException if either <code>v1</code> or
   * <code>v2</code> is not contained in this graph
   */
  public boolean areAdjacent (Vertex v1, Vertex v2) throws
  InvalidAccessorException;

  /**
   * Checks whether two edges have at least one common endpoint. 
   * (For example, parallel edges are considered adjacent, as are
   * two self-loops incident on a single vertex.)
   * @param e1 an edge
   * @param e2 an edge
   * @exception InvalidAccessorException if either <code>e1</code> or
   * <code>e2</code> is not contained in this graph
   * @return whether <code>e1</code> and <code>e2</code> are adjacent,
   * i.e., whether they have at least one common endvertex
   */
  public boolean areAdjacent (Edge e1, Edge e2) throws
  InvalidAccessorException;

  /**
   * @param v a vertex
   * @param e an edge
   * @return whether <code>v</code> and <code>e</code> are incident,
   * i.e., whether <code>v</code> is an endvertex of <code>e</code>
   * @exception InvalidAccessorException if either <code>v</code> or
   * <code>e</code> is not contained in this graph
   */
  public boolean areIncident (Vertex v, Edge e) throws
  InvalidAccessorException;


  
  /* vertex methods */

  /**
   * Gives the degree of a vertex, counting both directed and undirected
   * edges.
   *
   * @param v a vertex
   * @return the number of edges (directed and undirected) incident
   * with <code>v</code>
   * @exception InvalidAccessorException if <code>v</code> is 
   * not contained in this graph
   */
  public int degree (Vertex v) throws InvalidAccessorException;

  /**
   * Gives the degree of a vertex, counting all edges of the specified type.
   *
   * @param v a vertex
   * @param edgetype A constant from the <code>EdgeDirection</code> interface
   * @return the number of edges of the specified type incident
   * with <code>v</code>
   * @exception InvalidAccessorException if <code>v</code> is 
   * not contained in this graph
   * @see EdgeDirection
   */
  public int degree (Vertex v, int edgetype) throws InvalidAccessorException;

  /**
   * Lists all vertices adjacent to a particular vertex by any kind of
   * edge, with repeats corresponding to parallel edges.
   * 
   * @param v a vertex
   * @return an iterator over all vertices adjacent to <code>v</code> by undirected,
   * incoming and outgoing edges
   * @exception InvalidAccessorException if <code>v</code> 
   * is not contain in this graph
   */
  public VertexIterator adjacentVertices (Vertex v) throws
  InvalidAccessorException;

  /**
   * Lists all vertices adjacent to a particular vertex by all edges of
   * the types specified.  
   * 
   * @param v a vertex
   * @param edgetype A constant from the <code>EdgeDirection</code> interface
   * @return an iterator over all vertices adjacent to <code>v</code>
   * by edges of the specified type
   * @exception InvalidAccessorException if <code>v</code> is 
   * is not contained in this graph
   * @see EdgeDirection
   */
  public VertexIterator adjacentVertices (Vertex v, int edgetype) throws
  InvalidAccessorException;

  /**
   * @param v a vertex
   * @return an iterator over all edges incident on <code>v</code>
   * @exception InvalidAccessorException if <code>v</code> is not
   * contained in this graph
   */
  public EdgeIterator incidentEdges (Vertex v) throws
  InvalidAccessorException;

  /**
   * @param v a vertex
   * @param edgetype A constant from the <code>EdgeDirection</code> interface
   * @return an iterator over all edges of the specified type incident
   * on <code>v</code> 
   * @exception InvalidAccessorException if <code>v</code> is not
   * contained in this graph
   * @see EdgeDirection
   */
  public EdgeIterator incidentEdges (Vertex v, int edgetype) throws
  InvalidAccessorException;

  /**
   * @param v a vertex
   * @return any edge incident on <code>v</code>, or Edge.NONE if
   * there is no edge incident on <code>v</code>
   * @exception InvalidAccessorException if <code>v</code> is not
   * contained in this graph
   */
  public Edge anIncidentEdge (Vertex v) throws InvalidAccessorException;

  /**
   * @param v a vertex
   * @param edgetype A constant from the <code>EdgeDirection</code> interface
   * @return any edge of the specified type incident on <code>v</code>,
   * or Edge.NONE if there is no such edge incident on <code>v</code>
   * @exception InvalidAccessorException if <code>v</code> is not
   * contained in this graph
   * @see EdgeDirection
   */
  public Edge anIncidentEdge (Vertex v, int edgetype) throws
      InvalidAccessorException;

  /**
   * Gives all edges connecting two vertices.  If <code>v1==v2</code>,
   * gives all self-loops of the vertex, each reported twice as in
   * incidentEdges(.).
   * @param v1 a vertex
   * @param v2 a vertex
   * @return an iterator over the edges in common between
   * <code>v1</code> and <code>v2</code> 
   * @exception InvalidAccessorException if <code>v1</code> or <code>v2</code>
   * is not contained in this graph
   */
  public EdgeIterator connectingEdges (Vertex v1, Vertex v2) throws
  InvalidAccessorException;

  /** 
   * Gives an arbitrary edge from among those connecting the two
   * specified vertices.  If <code>v1==v2</code>, gives a self-loop
   * of the vertex.  If there is no edge that can be returned, returns Edge.NONE.
   * @param v1 a vertex
   * @param v2 a vertex
   * @return an edge between <code>v1</code> and <code>v2</code>,
   * or Edge.NONE if there is no such edge
   */
  public Edge aConnectingEdge( Vertex v1, Vertex v2 ) throws
  InvalidAccessorException;
  
  

  /* edge methods */

  /**
   * @param e an edge
   * @return an array (of size 2) containing the two endvertices of <code>e</code>;
   * if <code>e</code> is directed, the first element of the array is the origin of e
   * and the second element is the destination of <code>e</code>
   * @exception InvalidAccessorException if <code>e</code> is not
   * contained in this graph
   */
  public Vertex [] endVertices (Edge e) throws InvalidAccessorException;

  /**
   * @param v one endvertex of <code>e</code>
   * @param e an edge
   * @return the endvertex of <code>e</code> different from <code>v</code>
   * @exception InvalidVertexException if <code>v</code> is not an
   * endvertex of <code>e</code> 
   * @exception InvalidAccessorException if <code>v</code> or <code>e</code>
   * is not contained in this graph
   */
  public Vertex opposite (Vertex v, Edge e) throws InvalidVertexException,
  InvalidAccessorException;

  /**
   * @param e an edge
   * @return the origin vertex of <code>e</code>, if <code>e</code> is directed
   * @exception InvalidEdgeException if <code>e</code> is undirected
   * @exception InvalidAccessorException if <code>e</code> is not
   * contained in this graph
   */
  public Vertex origin (Edge e) throws InvalidEdgeException,
  InvalidAccessorException;

  /**
   * @param e an edge
   * @return the destination vertex of <code>e</code>, if
   * <code>e</code> is directed 
   * @exception InvalidEdgeException if <code>e</code> is undirected
   * @exception InvalidAccessorException if <code>e</code> is not
   * contained in this graph
   */
  public Vertex destination (Edge e) throws InvalidEdgeException,
  InvalidAccessorException;

  /**
   * @param e1 an edge
   * @param e2 an edge
   * @return any vertex that is an endpoint of both
   * <code>e1</code> and <code>e2</code>, or Vertex.NONE if there is
   * no such vertex
   * @exception InvalidAccessorException if <code>e1</code> or <code>e2</code>
   * is not contained in this graph
   */
  public Vertex aCommonVertex (Edge e1, Edge e2) throws
  InvalidAccessorException;



  /* direction methods */

  /**
   * @param e an edge
   * @return <code>true</code> if <code>e</code> is directed,
   * <code>false</code> otherwise
   * @exception InvalidAccessorException if <code>e</code> is not
   * contained in this graph
   */
  public boolean isDirected (Edge e) throws InvalidAccessorException;


}
