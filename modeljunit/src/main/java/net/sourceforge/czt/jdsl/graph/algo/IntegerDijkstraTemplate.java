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
import net.sourceforge.czt.jdsl.core.ref.ArrayHeap;
import net.sourceforge.czt.jdsl.core.ref.IntegerComparator;
import net.sourceforge.czt.jdsl.graph.api.*;



/**
 * Implementation of Dijkstra's algorithm using the template-method
 * pattern: the core functionality is coded in a few final methods
 * that call overridable methods to do some of the work.  The methods
 * of this class are in five categories:
 *
 * <ul>
 * 
 * <li>A method you must override to make the compiler happy: You must
 * override weight(Edge) to supply the algorithm with a weight for
 * every edge in the graph.  Note that Dijkstra's algorithm cannot
 * handle negative-weight edges.
 * 
 * <li>"Hook" methods that may be overridden to specialize the
 * algorithm to the application at hand: shortestPathFound(.),
 * edgeRelaxed(.), and vertexNotReachable(.).  For every vertex in the
 * graph (or every vertex you allow the algorithm to consider), either
 * shortestPathFound(.) or vertexNotReachable(.) will be called, and
 * will be called exactly once.  When that has occurred, the vertex is
 * considered to be "finished"; it will not be considered again by the
 * algorithm.  Finally, edgeRelaxed(.) will be called every time an
 * edge to an unfinished vertex is explored.
 * 
 * <li>Overridable methods that will need to be overridden more
 * rarely: See the comments for shouldContinue(), isFinished(.),
 * setLocator(.), getLocator(.), setEdgeToParent(.), newPQ(),
 * initMap(), incidentEdges(.), destination(.), vertices(), and
 * init(.) (which has a split role between this category of methods
 * and the next).
 *
 * <li>"Output" methods through which the user can test, after the
 * execution of the algorithm, whether a vertex is reachable from the
 * source, and retrieve the decorations of the vertices: See the
 * comments for isReachable(.), distance(.), and getEdgeToParent(.).
 * 
 * <li>Methods composing the core of the algorithm, which cannot be
 * overridden (or, in the case of init(.), should rarely be
 * overridden): You can run the algorithm in either of two ways.  If
 * you want to run the whole algorithm at once, use either version of
 * executeAll(.).  It will call doOneIteration() multiple times, and
 * doOneIteration() will call your overridden output methods as it
 * encounters vertices.  Instead of using executeAll(.), you can
 * single-step the algorithm by calling init(.) to initialize, then
 * calling doOneIteration() repeatedly.
 *
 * </ul>
 * 
 * Note that it is possible to confuse the algorithm by doing things
 * like modifying the graph, messing with the priority queue, or
 * changing edge weights while it is running.
 *
 * @version JDSL 2.1.1 
 * @author Mark Handy
 * @author Galina Shubina
 * @author Luca Vismara
 */
public abstract class IntegerDijkstraTemplate {

  // instance variables

  protected PriorityQueue pq_;
  protected InspectableGraph g_;
  protected Vertex source_;
  private final Integer ZERO = new Integer(0);
  private final Integer INFINITY = new Integer(Integer.MAX_VALUE);
  private final Object LOCATOR = new Object();
  private final Object DISTANCE = new Object();
  private final Object EDGE_TO_PARENT = new Object();

    
  // abstract instance method; must be overridden
    
  /** 
   * Must be overridden to supply a way of getting a positive weight
   * for every edge in the graph.  This method gets called by the
   * algorithm when the algorithm needs to know the weight of an
   * edge. Dijkstra's algorithm cannot handle negative weights.
   * Furthermore, although it works correctly with zero-weight edges,
   * some of the methods of this class make guarantees based on
   * assuming positive weights that they cannot make if there are
   * zero-weight edges.
   *
   * @param e Edge for which the algorithm needs to know a weight
   * @return Your application's weight for e
   */
  protected abstract int weight (Edge e);


  // instance methods that may be overridden for special applications

  /** 
   * Can be overridden to give you a notification when the shortest
   * path to a vertex is determined.  The algorithm calls this method
   * at most once per vertex, after the vertex has been "finished"
   * (i.e., when the path from s to the vertex is known).  The vertex
   * will never again be touched or considered by the algorithm.
   * <p>
   * Note that there is no corresponding get-method; the algorithm
   * does not need this information again, so the only constraints on
   * what you do with the information are those imposed by your
   * application.
   *
   * @param v Vertex that the algorithm just finished
   * @param vDist Distance of v from the source
   */
  protected void shortestPathFound (Vertex v, int vDist) {
    v.set(DISTANCE,new Integer(vDist));
  }
    
  /** 
   * Can be overridden in any application that involves unreachable
   * vertices.  Called every time a vertex with distance INFINITY
   * comes off the priority queue.  When it has been called once, it
   * should subsequently be called for all remaining vertices, until
   * the priority queue is empty.
   * <p>
   * Note that there is no corresponding get-method; the algorithm
   * does not need this information again, so the only constraints on
   * what you do with the information are those imposed by your
   * application.
   *
   * @param v Vertex which the algorithm just found to be unreachable
   * from the source
   */
  protected void vertexNotReachable (Vertex v) {
    v.set(DISTANCE,INFINITY);
    setEdgeToParent(v,Edge.NONE);
  }

  /** 
   * Can be overridden in any application where the edges considered
   * for the shortest-path tree matter.  Called every time an edge
   * leading to a vertex is examined (relaxed); this can happen many
   * times per vertex.  If udist + uvweight is less than vDist, there
   * is a shorter path to v, via u and uv, than the shortest path to v
   * previously known, so v is updated in the priority queue.  This
   * method notifies you before such a calculation is made, whether
   * the calculation results in an update or not.
   * <p>
   * For every vertex reachable from the source, except the source,
   * this method will be called at least once before the vertex is
   * finished.  Once a vertex has been finished, this method will
   * never be called for that vertex again.
   * <p>
   * Note that there is no corresponding
   * get-method; the algorithm does not need this information again,
   * so the only constraints on what you do with the information are
   * those imposed by your application.
   * @param u Vertex about to be finished, from which an edge to v
   * is being explored
   * @param uDist The final distance to u (will soon be passed as
   * svDist to shortestPathFound(.))
   * @param uv Edge being explored
   * @param uvWeight Weight of uv
   * @param v Vertex being investigated: the best-known-path to it
   * will be updated if the path via u and uv is better
   * @param vDist The present, possibly suboptimal, distance of v
   * from s
   */
  protected void edgeRelaxed (Vertex u, int uDist, Edge uv, int uvWeight,
			      Vertex v, int vDist) { }
    
    
  // instance methods that may be overridden for special applications,
  // but needn't be

  /** 
   * Can be overridden in any application where the full shortest-path
   * tree is not needed and the algorithm should terminate early.
   * executeAll(.) checks the return from this method before each call
   * to doOneIteration().  The default implementation just returns
   * <code>true</code>, so executeAll(.) continues until the full
   * shortest-path tree is built.  Notice that if you are calling
   * doOneIteration() manually, this method is irrelevant; only
   * executeAll(.) calls this method.
   *
   * @return Whether to continue running the algorithm
   */
  protected boolean shouldContinue () {
    return true;
  }

  /**
   * Tests whether a vertex has been reached.
   *
   * @param v a vertex
   * @return Whether v has been marked as finished
   */
  protected boolean isFinished (Vertex v) {
    return v.has(DISTANCE);
  }

  /** 
   * Can be overridden to supply a way of storing and retrieving one
   * locator per vertex.  Will be called only once per vertex, during
   * initialization.  The default implementation decorates each vertex
   * with its locator.
   *
   * @see #getLocator(Vertex)
   * @see Decorable#set(Object,Object)
   * @param v Vertex to decorate with a locator
   * @param vLoc the locator with which to decorate v
   */
  protected void setLocator (Vertex v, Locator vLoc) {
    v.set(LOCATOR,vLoc);
  }
    
  /** 
   * Can be overridden to supply a way of storing and retrieving one
   * locator per vertex.  This is the counterpart to setLocator(.)
   * but may be called many times.  The default implementation uses
   * the decoration of each vertex.  The algorithm calls this method
   * whenever it needs to update the best distance it knows for a
   * vertex, which requires updating the priority queue.
   *
   * @see #setLocator(Vertex,Locator)
   * @see Decorable#get(Object)
   * @param v Vertex previously decorated with a locator
   * @return Locator associated with v in the earlier setLocator(.) call
   */
  protected Locator getLocator (Vertex v) {
    return (Locator)v.get(LOCATOR);
  }

  /** 
   * Can be overridden to supply a way of storing and retrieving one
   * edge per vertex.  The default implementation decorates each vertex
   * with its edge.
   *
   * @see #getEdgeToParent(Vertex)
   * @see Decorable#set(Object,Object)
   * @param v Vertex to decorate with an edge
   * @param vEdge the with which to decorate v
   */
  protected void setEdgeToParent (Vertex v, Edge vEdge) {
    v.set(EDGE_TO_PARENT,vEdge);
  }
      
  /** 
   * Can be overridden to supply a priority queue of your
   * choosing, but the default implementation, which gives an empty   
   * net.sourceforge.czt.jdsl.core.ref.ArrayHeap, is probably sufficient for most
   * purposes.  The priority queue must be able to accept keys of
   * type Integer.  If you choose to override the method, 
   * for typical applications you should return an empty priority
   * queue.  If necessary, it can be preinitialized, although you
   * will need to accommodate that fact in other methods.
   * @return PriorityQueue to be used by the algorithm
   */
  protected PriorityQueue newPQ () {
    return new ArrayHeap(new IntegerComparator());
  }

  /** 
   * Can be overridden to initialize a locator-lookup data structure
   * of your choosing, but the default implementation, which decorates
   * each vertex with its locator, is probably sufficient for most
   * purposes.  This method is called by the algorithm before any call
   * to setLocator(.).  The best reason to override this method is
   * that you have some other way to implement set/getLocator(.).  In
   * that case, override this method to do any necessary
   * initialization of your data structure.<p>
   */
  protected void initMap () { }
    
  /** 
   * Can be overridden in any application where the default choice of
   * edges to consider at any vertex is not satisfactory.  The default
   * is to consider all outgoing and all undirected edges from a given
   * vertex.  Example:  if you have a directed graph but want to view it
   * as undirected for purposes of building a shortest-path tree, you
   * should override this method to read<br>
   * <code> return G.incidentEdges(v, EdgeDirection.IN | EdgeDirection.OUT);
   * </code>
   * @param v Vertex soon to be finished by the algorithm
   * @return All the interesting edges of v -- i.e., all edges whose
   * weights you want the algorithm to inspect in considering
   * alternative routes to vertices adjacent to v
   */
  protected EdgeIterator incidentEdges (Vertex v) {
    return g_.incidentEdges(v,EdgeDirection.OUT | EdgeDirection.UNDIR);
  }
    
  /** 
   * Can be overridden to supply the destination of an edge, although I
   * can't think of any reason to do so.  Presently implemented with
   * opposite(.), so it works even if the edge is incoming to v (see the
   * example under incidentEdges(.)).  Called by the core algorithm when
   * it is about to finish <code>origin</code> and needs all its
   * adjacent vertices.
   * @param origin Vertex soon to be finished by the algorithm
   * @param e Edge incident on <code>origin</code> according to
   * incidentEdges(.) 
   * @return the vertex opposite <code>origin</code> along
   * <code>e</code> 
   */
  protected Vertex destination (Vertex origin, Edge e) {
    return g_.opposite(origin,e);
  }

  /** 
   * Can be overridden to consider a subset of the vertices in the
   * graph, although I can't think of any reason to do so.  Note that
   * overriding this method will probably also require overriding
   * incidentEdges(.), in order to avoid edges leading to vertices not
   * in the subset.
   * @return Iterator over all vertices to be initially put in the
   * priority queue and eventually finished by the algorithm
   */
  protected VertexIterator vertices () {
    return g_.vertices();
  }


  // output instance methods
  
  /**
   * Tests whether a vertex is reachable from the source.  The method
   * can be invoked at any time during the single-step execution of
   * the algorithm.
   *
   * @param v a vertex
   * @return whether v is reachable from the source
   */
  public final boolean isReachable (Vertex v) {
    return v == source_
      || (v.has(EDGE_TO_PARENT) && v.get(EDGE_TO_PARENT) != Edge.NONE);
  }

  /**
   * Returns the distance of a vertex from the source.
   *
   * @param v a vertex
   * @return the distance of v from the source
   * @exception InvalidQueryException if v has not been reached yet
   */
  public final int distance (Vertex v) throws InvalidQueryException {
    try {
      return ((Integer)v.get(DISTANCE)).intValue();
    }
    catch (InvalidAttributeException iae) {
      throw new InvalidQueryException(v+" has not been reached yet");
    }
  }
    
  /** 
   * Can be overridden to supply a way of storing and retrieving one
   * edge per vertex.  This is the counterpart to setEdgeToParent(.)
   * but may be called many times.  The default implementation uses
   * the decoration of each vertex.  The algorithm calls this method
   * whenever it needs to update the best distance it knows for a
   * vertex, which requires updating the edge to parent.
   *
   * @see #setEdgeToParent(Vertex,Edge)
   * @see Decorable#get(Object)
   * @param v Vertex previously labeled with an edge
   * @return Edge associated with v in the earlier setEdgeToParent(.)
   * call
   * @exception InvalidQueryException if v is the source or has not
   * been reached yet
   */
  public Edge getEdgeToParent (Vertex v) throws InvalidQueryException {
    try {
      return (Edge)v.get(EDGE_TO_PARENT);
    }
    catch (InvalidAttributeException iae) {
      String s = (v == source_)
	? " is the source vertex" : " has not been reached yet";
      throw new InvalidQueryException(v+s);
    }
  }

  
  // instance methods composing the core of the algorithm; cannot be
  // changed

  /** 
   * Called automatically by executeAll(); must be called by the client
   * prior to the first call to doOneIteration() if finer-grained
   * control of the algorithm is needed.  The method initializes
   * instance variables and then puts all vertices in the PQ with
   * initial distances, and records their respective locators.  Can be
   * overridden, although I can't think of any reason to do so.
   * <p>
   * Calls the following methods that can be overridden:  newPQ(),
   * initMap(), vertices(), setLocator(.).
   *
   * @param g Graph on which to execute the algorithm
   * @param source Vertex at which to root the shortest-path tree
   */
  public void init (InspectableGraph g, Vertex source) {
    g_ = g;
    source_ = source;
    pq_ = newPQ();
    initMap();
    VertexIterator vi = vertices();
    while (vi.hasNext()) {
      Vertex u = vi.nextVertex();
      Integer ukey = (u == source_) ? ZERO : INFINITY;
      Locator uLoc = pq_.insert(ukey,u);
      setLocator(u,uLoc);
    }
  }

  /**
   * Removes the decorations from the vertices.  Its invocation is the
   * user's responsibility.
   */
  public void cleanup () {
    VertexIterator vi = vertices();
    while (vi.hasNext()) {
      vi.nextVertex().destroy(LOCATOR);
      try {
	vi.vertex().destroy(EDGE_TO_PARENT);
	vi.vertex().destroy(DISTANCE);
      }
      catch(InvalidAttributeException iae) { }
    }
  }
    
  /** 
   * Can be called manually to single-step the algorithm, but you must
   * call init(.) before the first call to this method.  Finishes one
   * vertex and updates all adjacent vertices.  If the vertex that
   * gets finished was reachable from the source, this method expands
   * the shortest-path tree by one vertex.
   */
  public final void doOneIteration () throws InvalidEdgeException {
    // from Q take u of minimum distance from source
    Integer minKey = (Integer)pq_.min().key();
    // remove a vertex with minimum distance from the source
    Vertex u = (Vertex)pq_.removeMin();   

    if (minKey == INFINITY)
      vertexNotReachable(u);
    else {   // the general case
      int uDist = minKey.intValue();
      shortestPathFound(u,uDist);
      int maxEdgeWeight = INFINITY.intValue()-uDist-1;
      // examine all the neighbors of u and update their distances
      EdgeIterator ei = incidentEdges(u);
      while (ei.hasNext()) {   // while u has more edges
	Edge uv = ei.nextEdge();
	int uvWeight = weight(uv);
	if (uvWeight < 0 || uvWeight > maxEdgeWeight)
	  throw new InvalidEdgeException
	    ("The weight of "+uv+" is either negative or causing overflow");
	Vertex v = destination(u,uv);
	Locator vLoc = getLocator(v);
	if (pq_.contains(vLoc)) {   // v is not finished yet
	  int vDist = ((Integer)vLoc.key()).intValue();
	  int vDistViaUV = uDist+uvWeight;
	  if (vDistViaUV < vDist) {   // relax
	    pq_.replaceKey(vLoc,new Integer(vDistViaUV));
	    setEdgeToParent(v,uv);
	  }
	  edgeRelaxed(u,uDist,uv,uvWeight,v,vDist);
	}
      }
    }
  }

  /**
   * Repeatedly calls method doOneIteration() until either the
   * priority queue is empty or method shouldContinue() returns false.
   */
  protected final void runUntil () {
    while (!pq_.isEmpty() && shouldContinue())
      doOneIteration();
  }

  /** 
   * The easiest way to use the algorithm is to use this method.
   * Calls init(.) once, then doOneIteration() repeatedly until
   * either the PQ is empty or shouldContinue() returns false.
   *
   * @param g Graph on which to execute the algorithm
   * @param source Vertex at which to root the shortest-path tree
   */
  public final void execute (InspectableGraph g, Vertex source) {
    init(g,source);
    runUntil();
  }
  
}   // class IntegerDijkstraTemplate
