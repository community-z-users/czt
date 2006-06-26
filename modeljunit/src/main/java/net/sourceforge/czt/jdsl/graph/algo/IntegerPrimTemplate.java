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
import net.sourceforge.czt.jdsl.graph.api.*;

/**
 * Implementation of the algorithm of Prim and Jarnik for finding a
 * minimum spanning tree, using the template-method
 * pattern:  the core functionality is coded in a few final methods
 * that call overridable methods to do some of the work.  The methods
 * of this class are in four categories:
 * <ul>
 * 
 * <li>a method you must override to make the compiler happy:  
 * You must override weight(Edge) to supply the algorithm with a
 * weight for every edge in the graph.  Note that the Prim-Jarnik
 * algorithm cannot handle negative-weight edges.
 * 
 * <li>"output" methods that you must, realistically speaking, override
 * in order to get useful information out of the algorithm and into
 * your application domain:  You will need
 * to override at least one of treeEdgeFound(.), relaxingEdge(.),
 * and vertexNotReachable(.).  For every vertex in the graph (or
 * every vertex you allow the algorithm to consider), either
 * treeEdgeFound(.) or vertexNotReachable(.) will be called, and
 * will be called exactly once.  When that has occurred, the vertex is
 * considered to be "finished"; it will not be considered again by the
 * algorithm.  Finally, relaxingEdge(.) will be
 * called every time an edge to an unfinished vertex is explored.
 * 
 * <li>overridable methods that will need to be overridden only
 * for special applications:  See the comments for shouldContinue(),
 * setLocator(.), getLocator(.), newPQ(), initMap(), incidentEdges(.),
 * destination(.), allVertices(), and init(.) (which has a split role
 * between this category of methods and the next).
 * 
 * <li>methods composing the core of the algorithm, which cannot be
 * overridden (or, in the case of init(.), should rarely be overridden):
 * You can run the
 * algorithm in either of two ways.  If you want to run the whole
 * algorithm at once, use either version of executeAll(.).  It will call
 * doOneIteration() multiple times, and doOneIteration() will call
 * your overridden output methods as it encounters vertices.  Instead
 * of using executeAll(.), you can single-step the algorithm by
 * calling init(.) to initialize, then calling doOneIteration() repeatedly.
 * </ul>
 * 
 * Note that it is possible to confuse the algorithm by doing things
 * like modifying the graph, messing with the priority queue, or changing
 * edge weights while it is running.
 *
 * @author Mark Handy
 * @author Galina Shubina
 */

public abstract class IntegerPrimTemplate {
    public IntegerPrimTemplate() { }
    
    protected PriorityQueue Q;
    protected InspectableGraph G;
    protected Vertex source;
    protected Integer ZERO;
    protected Integer INFINITY;
    protected java.util.Hashtable locators;
    protected int treeWeight;

    private static class VEPair { // v and its best-so-far incoming e
	VEPair( Vertex v, Edge e ) { vert=v; edge=e; }
	private Vertex vert;
	private Edge edge;
    }
    
    
    
    // method that must be overridden to satisfy the compiler
    
    /** 
     * Must be overridden to supply a way of getting a positive weight
     * for every edge in the graph.  This method gets called by the
     * algorithm when the algorithm needs to know the weight of an
     * edge. Prim's algorithm cannot handle negative
     * weights.  Furthermore, although it works correctly with
     * zero-weight edges, some of the methods of this class make
     * guarantees based on assuming positive weights that they cannot
     * make if there are zero-weight edges.
     * @param e Edge for which the algorithm needs to know a weight
     * @return Your application's weight for e
     */
    protected abstract int weight( Edge e );



    

    // "output" methods, at least one of which must, realistically speaking,
    // be overridden in order to get output from the algorithm

    /** 
     * Can be overridden to give you a notification when a vertex is
     * added to the minimum spanning tree.  The algorithm calls this
     * method at most once per vertex, after the vertex has been
     * "finished" (i.e., when the path from s to the vertex is known).  The
     * vertex will never again be touched or considered by the
     * algorithm.
     * <p>
     * Note that there is no corresponding get-method; the
     * algorithm does not need this information again, so the
     * only constraints on what you do with the information are those
     * imposed by your application.
     * @param v Vertex that the algorithm just finished
     * @param vparent Edge leading into v in the minimum spanning tree
     * @param treeWeight the total weight of all edges known to be
     * in the tree at this point in the execution of the algorithm, including
     * vparent
     */
    protected void treeEdgeFound( Vertex v, Edge vparent, int treeWeight ) { }
    
    /** 
     * Can be overridden in any application that involves unreachable
     * vertices.  Called every time a vertex with distance INFINITY comes
     * off the priority queue.  When it has been called once, it should
     * subsequently be called for all remaining vertices, until the 
     * priority queue is empty.
     * <p>
     * Note that there is no corresponding get-method; the
     * algorithm does not need this information again, so the
     * only constraints on what you do with the information are those
     * imposed by your application.
     * @param v Vertex which the algorithm just found to be
     * unreachable from the source
     */
     protected void vertexNotReachable( Vertex v ) { }
    
    /** 
     * Can be overridden in any application where the edges considered
     * for the minimum spanning tree matter.  Called every time an edge
     * leading to a vertex is examined (relaxed); this can happen many
     * times per vertex.  If uvweight is less than vdist, then uv is a
     * better tree edge to v than the best edge to
     * v previously known, so v is updated in the priority queue.
     * This method notifies you before such a calculation is made,
     * whether the calculation results in an update or not.
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
     * @param uv Edge being explored
     * @param uvweight Weight of uv
     * @param v Vertex being investigated: the best-known-edge to it
     * will be updated if the uv is a better edge
     * @param vdist The present, possibly suboptimal, distance of v
     * from the partially built spanning tree
     */
    protected void relaxingEdge( Vertex u, 
				 Edge uv, int uvweight,
				 Vertex v, int vdist ) { }

    
    
    
    
    
    // methods that may be overridden for special applications,
    // but needn't be

    /** 
     * Can be overridden in any application where the full
     * minimum spanning tree is not needed and the algorithm should
     * terminate early.  executeAll(.) checks the return from this
     * method before each call to doOneIteration().  The default
     * implementation just returns <code>true</code>, so 
     * executeAll(.) continues until the full tree is
     * built.  Notice that if you are calling doOneIteration()
     * manually, this method is irrelevant; only executeAll(.) calls
     * this method. 
     * @return Whether to continue running the algorithm
     */
    protected boolean shouldContinue() {
	return true;
    }

    /** 
     * Can be overridden to supply a way of storing and retrieving
     * one locator per vertex.  Will be called exactly once per vertex,
     * during initialization.  The default implementation uses the
     * java.util.Hashtable initialized by initMap() to store one locator per vertex. 
     * @see #getLocator(Vertex)
     * @see #initMap()
     * @param u Vertex to label with a locator
     * @param ulocInPQ the label
     */
    protected void setLocator( Vertex u, Locator ulocInPQ ) {
	locators.put( u, ulocInPQ );
    }
    
    /** 
     * Can be overridden to supply a way of storing and retrieving one
     * locator per vertex.  This is the counterpart to setLocator(.)
     * but may be called many times.  The default implementation
     * queries the java.util.Hashtable mentioned in setLocator(.). The
     * algorithm calls this method whenever it needs to update the
     * best distance it knows for a vertex, which requires updating
     * the priority queue. 
     * @see #setLocator(Vertex,Locator)
     * @param u Vertex previously labeled with a locator
     * @return Locator associated with u in the earlier setLocator(.) call
     */
    protected Locator getLocator( Vertex u ) {
	return (Locator) locators.get(u);
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
    protected PriorityQueue newPQ() {
	return new net.sourceforge.czt.jdsl.core.ref.ArrayHeap
	    ( new net.sourceforge.czt.jdsl.core.ref.IntegerComparator() );
    }
    
    /** 
     * Can be overridden to initialize a locator-lookup data structure
     * of your choosing, but the default implementation, which uses a
     * java.util.Hashtable, is probably sufficient for most purposes.
     * This method is called by the algorithm before any call to
     * setLocator(.).  The best reason to override this method is that
     * you have some way other than a java.util.Hashtable to implement
     * set/getLocator(.).  In that case, override this method to
     * do any necessary initialization of your data structure.
     * <p>
     * Note that the algorithm never removes anything from
     * <code>locators</code>, so if you want to execute the algorithm
     * repeatedly, it is probably unwise to return the same data structure
     * repeatedly from this method.
     */
    protected void initMap() {
	locators = new java.util.Hashtable();
    }
    
    /** 
     * Can be overridden in any application where the default choice of
     * edges to consider at any vertex is not satisfactory.  The default
     * is to consider all edges from a given vertex, directed and undirected.
     * Example:  if you want to build an MST on just the undirected
     * edges of your graph, you should override this method to read<br>
     * <code> return G.incidentEdges( v, EdgeDirection.UNDIR );
     * </code>
     * @param v Vertex soon to be finished by the algorithm
     * @return All the interesting edges of v -- i.e., all edges whose
     * weights you want the algorithm to inspect in considering
     * alternative edges to vertices adjacent to v
     */
    protected EdgeIterator incidentEdges( Vertex v ) {
	return G.incidentEdges( v );
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
    protected Vertex destination( Vertex origin, Edge e ) {
	return G.opposite( origin, e );
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
    protected VertexIterator allVertices() {
	return G.vertices();
    }

    /** 
     * Can be overridden to handle edges that have zero or
     * negative weights.  The Prim-Jarnik algorithm is not guaranteed
     * to work correctly in the presence of negative-weight edges.
     * In the present of zero-weight edges, the algorithm works
     * correctly, but some guarantees of other methods of this
     * override this method to throw an exception or to fix 
     * the problem and return the weight the algorithm should use for
     * edge uv.  Whatever weight you return the algorithm will use,
     * without checking it.  The default behavior is to throw an
     * InvalidEdgeException if uvweight is negative, and to
     * return 0 if uvweight is 0 -- that is, to allow zero-weight
     * edges. 
     * @param u Vertex being finished when the bad weight was
     * discovered 
     * @param uv Edge for which weight(uv) returned a zero or negative
     * value 
     * @param uvweight The weight returned from weight(uv)
     * @return Weight the algorithm should use for uv (can be equal to
     * uvweight) (the default is to return 0 only if uvweight is 0)
     * @exception RuntimeException Any exception you want to throw to
     * indicate a bad weight (the default is to throw an
     * InvalidEdgeException only if uvweight is negative)
     */
     protected int badWeight( Vertex u, Edge uv, int uvweight ) {
	if( uvweight < 0 ) throw new InvalidEdgeException
			       ( "negative weight on edge" );
	else return 0;
    }

    /** 
     * Called automatically by executeAll(); must be called by the client
     * prior to the first call to doOneIteration() if finer-grained
     * control of the algorithm is needed.  The method initializes
     * instance variables and then puts all vertices in the PQ with
     * initial distances, and records their respective locators.  Can be
     * overridden, although I can't think of any reason to do so.
     * <p>
     * Calls the following methods that can be overridden:  newPQ(),
     * initMap(), allVertices(), setLocator(.).
     * @param g Graph on which to execute the algorithm
     * @param src Vertex at which to root the minimum spanning tree
     * @param infinity Distance with which all other vertices will be
     * labelled initially; must be greater than any edge weight
     */
    public void init( InspectableGraph g,
		      Vertex src,
		      int infinity ) {
	G = g;
	source = src;
	ZERO = new Integer(0);
	INFINITY = new Integer(infinity);
	Q = newPQ();
	initMap(); // by default, initializes the "locators" variable
	treeWeight = 0;
	VertexIterator pv = allVertices();
	while( pv.hasNext() ) {
	    Vertex u = pv.nextVertex();
	    Integer ukey;
	    if( u==source ) ukey = ZERO;
	    else ukey = INFINITY;
	    Locator uloc = Q.insert( ukey, new VEPair(u,null) );
	    setLocator( u, uloc );
	}
    }
    



    // methods composing the core of the algorithm, cannot be changed
    
    /** 
     * Can be called manually to single-step the
     * algorithm, but you must call init(.) before the first call to this
     * method.  Finishes one vertex and updates all adjacent
     * vertices.  If the vertex that gets finished was reachable from
     * the source, this method expands the minimum spanning tree by
     * one vertex.
     */
    public final void doOneIteration() {
	    
	// from Q take u of minimum distance from tree
	Locator uloc = Q.min();  Q.removeMin();
	VEPair ue = (VEPair) uloc.element(); // u and its parent edge
	Vertex u = ue.vert;

	if( uloc.key()==INFINITY ) vertexNotReachable(u); // u is finished
	else { // the general case
	    
	    // examine all the neighbors of u and update their distances
	    EdgeIterator pe = incidentEdges(u);
	    while( pe.hasNext() ) {
		Edge uv = pe.nextEdge();
		int uvweight = weight(uv);
		if( uvweight < 1 ) uvweight = badWeight( u, uv, uvweight );
		Vertex v = destination( u, uv );
		Locator vloc = getLocator( v );
		if( Q.contains(vloc) ) { // relax
		    int vdist = ( (Integer)vloc.key() ).intValue();
		    relaxingEdge( u, uv, uvweight, v, vdist );
		    if( uvweight < vdist ) {
			Q.replaceKey( vloc, new Integer(uvweight) );
			( (VEPair) vloc.element() ).edge = uv;
		    }
		}
	    } // while u has more edges

	    if( ue.edge != null ) treeWeight += weight( ue.edge );
	    treeEdgeFound( u, ue.edge, treeWeight ); // u is finished

	}
    }

    /** 
     * The easiest way to use the algorithm is to use this method.
     * Calls init(.) once, then doOneIteration() repeatedly until
     * either the PQ is empty or shouldContinue() returns false.
     */
    public final void executeAll( InspectableGraph g,
				  Vertex src,
				  int infinity ) {
	init( g, src, infinity );
	while( ! Q.isEmpty() && shouldContinue() ) doOneIteration();
    }
    
    /** 
     * Just like the other version of executeAll(.), but with 
     * infinity=Integer.MAX_VALUE 
     */
    public final void executeAll( InspectableGraph g,
				  Vertex src ) {
	init( g, src, Integer.MAX_VALUE );
	while( ! Q.isEmpty() && shouldContinue() ) doOneIteration();
    }
    
} // class IntegerPrimTemplate



