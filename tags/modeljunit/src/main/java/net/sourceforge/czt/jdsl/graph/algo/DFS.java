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

/**
 * algorithmic template may be extended to solve a variety of
 * problems on either directed or undirected graphs.
 * 
 * <p>This algorithm runs in O(V+E) time where V is the number of
 * vertices in the graph, and E is the number of edges. It also uses
 * O(V+E) additional space to store data about the vertices and edges
 * during the computation. To this end, it is expected that the
 * <code>Edges</code> and <code>Vertices</code> implement the
 * <code>Decorable</code> interface.
 *
 * <p>This DFS also conforms to the CLR version in that it maintains
 * "parent references" to the previous Vertex in a DFS path as well
 * as "start-" and "finish times".
 *
 * @author Natasha Gelfand
 * @author Keith Schmidt (kas)
 *
 * @version JDSL 2.1.1 
 */
public class DFS {

  /*********************
   * CONSTANTS
   *********************/

  /** 
    * Constant used as key to look up an edge's type.
    * (UNSEEN, TREE_EDGE, BACK_EDGE, FORWARD_EDGE, or CROSS_EDGE)  
    */
  public static final Object EDGE_TYPE = new Object();

  /** 
    * Constant signifying that an edge has not yet been seen.  
    */
  public static final Object UNSEEN = new Object();

  /** 
    * Constant signifying that a marked edge is a tree edge.  
    */
  public static final Object TREE_EDGE = new Object();

  /**
   * Constant signifying that a marked edge is a back edge.
   */
  public static final Object BACK_EDGE = new Object();

  /**
   * Constant signifying that a marked edge is a forward edge.
   */
  public static final Object FORWARD_EDGE = new Object();

  /** 
    * Constant signifying that a marked edge is a cross edge.
    */
  public static final Object CROSS_EDGE = new Object();
  
  
  /** 
    * Constant used as key to look up an vertex's status.
    * (UNVISITED, VISITING, or VISITED)  
    */
  public static final Object VERTEX_STATUS = new Object();
  /** 
    * Constant signifying that an vertex has not been visited
    */
  public static final Object UNVISITED = new Object();

  /** 
    * Constant signifying that an vertex is being visited
    */
  public static final Object VISITING = new Object();

  /** 
    * Constant signifying that an vertex has been visited
    */
  public static final Object VISITED = new Object();

  
  /**
    * Constant used as key to look up the parent of a vertex.
    */
  public static final Object PARENT = new Object();
  
  /** 
    * Constant used as key to look up the tree to which a Vertex
    * belongs.
    */
  public static final Object TREE_NUMBER = new Object();
  
  /**
    * Constant used as key to look up the start time of a vertex.
    */
  public static final Object START_TIME = new Object();
  
  /**
    * Constant used as key to look up the finish time of a vertex.
    */
  public static final Object FINISH_TIME = new Object();

  /*********************
   * Instance Variables
   *********************/

  /**
    * The graph being traversed.
    */
  protected InspectableGraph graph_;
  
  /**
    * The result of the traversal.
    */
  protected Object visitResult_;
  
  /**
    * The number of the DFS tree being traversed.
    */
  protected int treeNum_ = 0;

  /**
    * The time stamp for when a Vertex is discovered, and when the 
    * visit is finished.
    */
  private int time_ = 0;


  /**
    * Runs the depth first search algorithm on a graph.
    *
    * @param g An <code>InspectableGraph</code> on which to run a depth first
    * search.
    * @param start The <code>Vertex</code> at which to start the depth first
    * search.
    */
  public void execute(InspectableGraph g, Vertex start) {
    graph_ = g;
    // initialize all vertices.
    for (VertexIterator verticesInGraph = graph_.vertices();
	 verticesInGraph.hasNext(); ) {
      Vertex v = (verticesInGraph.nextVertex());
      mark(v, UNVISITED);
      setStartTime(v, new Integer(0) );
      setFinishTime(v, null );
      setParent(v, null);
    }
    // initialize all edges.
    for (EdgeIterator edgesInGraph = graph_.edges();
	 edgesInGraph.hasNext(); ) {
      mark(edgesInGraph.nextEdge(), UNSEEN);
    }
    // run a DFS on the source
    dfsVisit(start);
    // ensure that all vertices are hit, if the algo is not done.
    for (VertexIterator verticesInGraph = graph_.vertices();
	 verticesInGraph.hasNext(); ) {
      Vertex newSource = verticesInGraph.nextVertex();
      if (!isDone()) {
	if (isUnvisited(newSource)) {
	  treeNum_++;
	  dfsVisit(newSource);
	}
      }
    }
  }

  /**
    * Execute a DFS without specifying an initial source vertex.
    */
  public void execute(InspectableGraph g) {
    this.execute(g, g.aVertex());
  }

  /**
    * Performs a recursive depth-first search starting at <code>v</code>
    * @param v - the vertex at which to start a DFS.
    */
  protected void dfsVisit(Vertex v) {
    startVisit(v);
    mark(v, VISITING);
    setTreeNumber(v, new Integer(treeNum_));
    setStartTime(v, new Integer(time_++));
    // check all incident edges
    for (EdgeIterator adjEdges = interestingIncidentEdges(v);
	 adjEdges.hasNext(); ) {
      Edge nextEdge = adjEdges.nextEdge();
      checkEdge(nextEdge, v);// ensure nextEdge is valid.
      Vertex w = graph_.opposite(v, nextEdge);
      if (isUnseen(nextEdge)) { // found an unexplored edge, explore it
	if (isUnvisited(w)) { // w is unexplored, this is a discovery edge
	  mark(nextEdge, TREE_EDGE);
	  traverseTreeEdge(nextEdge, v);
	  if (!isDone()) {
	    setParent(w, v);
	    dfsVisit(w);
	  }
	} 
	else { // w is explored.
	  if (startTime(w).intValue() < startTime(v).intValue()) {
	    if (finishTime(w) == null) {
	      // we are below w in its DFS tree
	      mark(nextEdge, BACK_EDGE);
	      traverseBackEdge(nextEdge, v);
	    }
	    else if (finishTime(w).intValue() < startTime(v).intValue()) { 
	      //we are neither above nor below w in its DFS tree.
	      mark(nextEdge, CROSS_EDGE);
	      traverseCrossEdge(nextEdge, v);
	    }
	    else {
	      throw new AnachronismException("ERROR: the time intervals of "+v+" and "+w+ " are neither disjoint nor nested.");
	    }
	  }// END startTime(w) < startTime(v)
	  else if (startTime(w).intValue() > startTime(v).intValue()) {
	    // we are above w in its DFS tree
	    if (finishTime(w) == null) {
	      throw new AnachronismException("ERROR: "+w+" is a child of "+v+" whose visit never finished.");
	    }
	    else {
	      mark(nextEdge, FORWARD_EDGE);
	      traverseForwardEdge(nextEdge, v);
	    }
	  }
	  else { // startTime(w) == startTime(v)
	    if (v == w) {
	      // self loops are back edges.
	      mark(nextEdge, BACK_EDGE);
	      traverseBackEdge(nextEdge, v);
	    }
	    else {
	      throw new AnachronismException("ERROR: the time intervals of "+v+" and "+w+" begin at the same number.");
	    }
	  }
	}
      }
    }
    finishVisit(v);
    mark(v, VISITED);
    setFinishTime(v, new Integer(time_++));
  }

  /************************
   * CONVENIENCE METHODS
   ************************/

  /**
    * Assigns the "Start time" of a Vertex.
    */
  private void setStartTime(Vertex v, Integer sTime) {
    v.set(START_TIME, sTime);
  }
  
   /**
    * Assigns the "Finish time" of a Vertex.
    */
  private void setFinishTime(Vertex v, Integer fTime) {
    v.set(FINISH_TIME,fTime);
  }

   /**
    * Stores the parent Vertex of another Vertex
    */
  private void setParent(Vertex v, Vertex par) {
    v.set(PARENT, par);
  }

   /**
    * Stores an index representing a DFS tree.
    */
  private void setTreeNumber(Vertex v, Integer treeNum) {
    v.set(TREE_NUMBER, treeNum);
  }

   /**
    * Called when a vertex's status changes.
    */
  private void mark(Vertex v, Object state) {
    v.set(VERTEX_STATUS, state);
  }

   /**
    * Marks an edge as traversed.
    */
  private void mark(Edge e, Object type) {
    e.set(EDGE_TYPE, type);
  }

  /**
   * Ensures that a given Edge is valid (i.e. incident on a given
   * Vertex v).
   */
  private void checkEdge(Edge e, Vertex v) {
    Vertex[] ends = graph_.endVertices(e);
    if ( !((ends[0] == v) || (ends[1] == v)) )
      throw new InvalidEdgeException("Edge "+e+" not incident on Vertex "+v);
  }

  /********************************************
   * PUBLIC IMPLEMENTATION-INDEPENDENT METHODS
   ********************************************/

  /**
   * Returns the "Start time" of a Vertex.
   * @param v - the Vertex to check.
   */
  public Integer startTime(Vertex v) {return (Integer)v.get(START_TIME);}
  
  /**
   * Returns the "Finish time" of a Vertex.
   * @param v - the Vertex to check.
   */
  public Integer finishTime(Vertex v) {return (Integer)v.get(FINISH_TIME);}

  /**
   * Retrieves the parent Vertex of a Vertex
   * @param v - the Vertex whose parent to find.
   */
  public Vertex parent(Vertex v) {
    return (Vertex)v.get(PARENT);
  }

  /**
   * Retrieves an index representing a connected DFS component. These
   * numbers start at 0 and are incremented after a component is
   * fully traversed. If a certain start Vertex is specified, it will
   * be the root of a DFS tree (defined be Vertices and Tree Edges)
   * with number 0.
   * @param v - the Vertex to check.
   */
  public Integer treeNumber(Vertex v) {
    return (Integer)v.get(TREE_NUMBER);
  }
  
  /**
   * Accesses the current status of the given Vertex. If the Vertex
   * has no status, <code>null</code> is returned.  
   * @param v - the Vertex to check.
   */
  public Object status(Vertex v) {
    if (v.has(VERTEX_STATUS))
      return v.get(VERTEX_STATUS);
    return null;
  }
  
  /**
   * Tests if a vertex has not been visited.
   * @param v - the Vertex to check.
   */
  public boolean isUnvisited(Vertex v) {
    if ((v.has(VERTEX_STATUS)) &&
	(v.get(VERTEX_STATUS) == UNVISITED))
      return true;
    return false;
  }

  /**
   * Tests if a vertex is being visited.
   * @param v - the Vertex to check.
   */
  public boolean isVisiting(Vertex v) {
    if ((v.has(VERTEX_STATUS)) &&
	(v.get(VERTEX_STATUS) == VISITING))
      return true;
    return false;
  }

  /**
   * Tests if a vertex has been visited.
   * @param v - the Vertex to check.
   */
  public boolean isVisited(Vertex v) {
    if ((v.has(VERTEX_STATUS)) &&
	(v.get(VERTEX_STATUS) == VISITED))
      return true;
    return false;
  }

  /**
   * Accesses the current type of the given Edge. If the Edge
   * has no type, <code>null</code> is returned.  
   * @param e - the Edge to check.
   */
  public Object type(Edge e) {
    if (e.has(EDGE_TYPE))
      return e.get(EDGE_TYPE);
    return null;
  }
 

  /**
   * Tests if an edge has been seen yet.
   * @param e - the Edge to check.
   */
  public boolean isUnseen(Edge e) {
    if ((e.has(EDGE_TYPE)) && 
	(e.get(EDGE_TYPE) == UNSEEN))
      return true;
    return false;
  }

  /**
   * Tests if an edge is a tree edge.
   * @param e - the Edge to check.
   */
  public boolean isTreeEdge(Edge e) {
    if ((e.has(EDGE_TYPE)) && 
	(e.get(EDGE_TYPE) == TREE_EDGE))
      return true;
    return false;
  }

  /**
   * Tests if an edge is a back edge.
   * @param e - the Edge to check.
   */
  public boolean isBackEdge(Edge e) {
    if ((e.has(EDGE_TYPE)) && 
	(e.get(EDGE_TYPE) == BACK_EDGE))
      return true;
    return false;
  }

  /**
   * Tests if an edge is a forward edge.
   * @param e - the Edge to check.
   */
  public boolean isForwardEdge(Edge e) {
    if ((e.has(EDGE_TYPE)) && 
	(e.get(EDGE_TYPE) == FORWARD_EDGE))
      return true;
    return false;
  }

  /**
   * Tests if an edge is a cross edge.
   * @param e - the Edge to check.
   */
  public boolean isCrossEdge(Edge e) {
    if ((e.has(EDGE_TYPE)) && 
	(e.get(EDGE_TYPE) == CROSS_EDGE))
      return true;
    return false;
  }

  /** 
    * Cleans up all decorations stored in the provided graph.  This
    * should be called after the user has completely finished
    * everything resulting from a single DFS execution.  
    */
  public void cleanup() {
    //remove all level numbers from the graph.
    VertexIterator vertices = graph_.vertices();
    while( vertices.hasNext() ) {
      Vertex currentVertex = vertices.nextVertex();
      //Test if the vertex is decorated, because if the graph is
      //functionally disconnected (i.e. interestingEdges isn't very
      //smart), all vertices may not be visited.
      if(currentVertex.has(VERTEX_STATUS))
	currentVertex.destroy(VERTEX_STATUS);

      if (currentVertex.has(PARENT))
	currentVertex.destroy(PARENT);

      if (currentVertex.has(START_TIME))
	currentVertex.destroy(START_TIME);

      if (currentVertex.has(FINISH_TIME))
	currentVertex.destroy(FINISH_TIME);

      if (currentVertex.has(TREE_NUMBER))
	currentVertex.destroy(TREE_NUMBER);
    }
    //remove all edge classifications from edges
    EdgeIterator edges = graph_.edges();
    while(edges.hasNext()) {
      Edge currentEdge = edges.nextEdge();
      //Test if the edge is decorated, because if the graph is
      //functionally disconnected (i.e. interestingEdges isn't very
      //smart), all vertices may not be visited.
      if(currentEdge.has(EDGE_TYPE))
	currentEdge.destroy(EDGE_TYPE);
    }  
  }

  /*************************************
   * IMPLEMENTATION-SPECIFIC METHODS
   *************************************/

   /**
    * Called when a vertex is visited.  Can be overridden by a subclass.
    */
  protected void startVisit(Vertex v) {}

   /**
    * Called when a discovery edge is traversed.  Can be overridden by a
    * subclass.
    */
  protected void traverseTreeEdge(Edge e, Vertex from) {}

   /**
    * Called when a back edge is traversed.  Can be overridden by a
    * subclass.  
    */
  protected void traverseBackEdge(Edge e, Vertex from) {}

   /**
    * Called when a forward edge is traversed.  Can be overridden
    * by a subclass.  
    */
  protected void traverseForwardEdge(Edge e, Vertex from) {}

   /**
    * Called when a cross edge is traversed.  Can be overridden by a
    * subclass.
    */
  protected void traverseCrossEdge(Edge e, Vertex from) {}

   /**
    * Tests if the depth first search is done.  Can be overridden by a
    * subclass.
    */
  protected boolean isDone() { return false; }

   /**
    * Called when the search has finished with the vertex.  Can be
    * overridden by a subclass.
    */
  protected void finishVisit(Vertex v) {}

  /**
   * A method that returns an iterator over those edges incident
   * to the parameter vertex in the graph which should be considered for
   * exploration.  Subclasses of DFS may implement this method so as to
   * traverse edges as though they were undirected or to traverse the
   * directed edges in the forward or reverse directions, or to in some
   * other way hand pick which edges were of interest for exploration.
   *
   * @param v The vertex for which interesting incident edges shouldbe
   * returned
   * @return EdgeIterator An Iterator over interesting edges incident to the
   * parameter Vertex
   */
  protected EdgeIterator interestingIncidentEdges(Vertex v) 
    { return graph_.incidentEdges(v);}
}

