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
// Jan 2006: marku@cs.waikato.ac.nz, renamed two local variables
//   from 'enum' to 'edges', because enum is a keyword of Java 1.5.


package net.sourceforge.czt.jdsl.graph.ref;

import net.sourceforge.czt.jdsl.core.api.*;
import net.sourceforge.czt.jdsl.graph.api.*;



/**
  * An implementation of many of the methods of InspectableGraph in terms
  * of a few primitives.  Note that that says "InspectableGraph," not "Graph,"
  * but that this class extends AbstractPositionalContainer, which
  * implements replaceElements(.).  All the methods implemented here
  * belong to InspectableGraph.
  * <p>
  * The implementor must define the primitives called by the
  * functions here.  In addition, the implementor must define any
  * primitives needed for <code>AbstractPositionalContainer</code>
  * not defined here.
  * <p>
  * In several places when the AbstractGraph calls a method that the
  * implementer must define, the AbstractGraph is relying on the
  * implementer also checking the input vertex or edge for validity.
  * <p>
  * The complexities of the methods implemented here depend on
  * the complexities of the underlying methods.  Therefore, the
  * complexity documented for each method below is based on
  * suppositions about the underlying implementation.
  *
 * @author Mark Handy
 * @author Benoit Hudson
  * @version JDSL 2.1.1 
  */
abstract public class AbstractGraph
extends net.sourceforge.czt.jdsl.core.ref.AbstractPositionalContainer
implements InspectableGraph
{
    
    protected AbstractGraph() { }

    /**
     * Built on numVertices() and numEdges().
     * <p>
     * O(1)
     *
     * @see InspectableGraph#numVertices()
     * @see InspectableGraph#numEdges()
     */

    public int size() {
	return numVertices()+numEdges();
    }

    /**
     * Built on vertices() and edges().
     * <p>
     * O(V+E)
     *
     * @see InspectableGraph#vertices()
     * @see InspectableGraph#edges()
     */
    public PositionIterator positions() {
	return new PP_to_P_MergerIterator( vertices(), edges() );
    }

    /**
     * Built on edges() and isDirected(.)
     * <p>
     * O(E)
     *
     * @see InspectableGraph#edges()
     * @see InspectableGraph#isDirected(Edge)
     */
    public EdgeIterator directedEdges() {
	Sequence accum = new net.sourceforge.czt.jdsl.core.ref.NodeSequence();
	EdgeIterator edges = edges();
	while(edges.hasNext()) {
	    Edge e = edges.nextEdge();
	    if( isDirected(e) ) {
	        accum.insertLast(e);
	    }
	}
	return new EdgeIteratorAdapter( accum.elements() );
    }

    /**
     * Built on edges() and isDirected(.)
     * <p>
     * O(E)
     *
     * @see InspectableGraph#edges()
     * @see InspectableGraph#isDirected(Edge)
     */
    public EdgeIterator undirectedEdges() {
	Sequence accum = new net.sourceforge.czt.jdsl.core.ref.NodeSequence();
	EdgeIterator edges = edges();
	while(edges.hasNext()) {
	    Edge e = edges.nextEdge();
	    if( ! isDirected(e) ) {
	        accum.insertLast(e);
	    }
	}
	return new EdgeIteratorAdapter( accum.elements() );
    }
    
    /**
     * Built on incidentEdges(.)
     * <p>
     * O(deg[v])
     *
     * @see InspectableGraph#incidentEdges(Vertex)
     */
    public VertexIterator adjacentVertices (Vertex v) {
	EdgeIterator edges = incidentEdges (v); 
	return _adjacentVertices(v, edges);
    }
    
    /**
     * Built on incidentEdges(.)
     * <p>
     * O(deg[v])
     *
     * @see InspectableGraph#incidentEdges(Vertex)
     */
    public VertexIterator adjacentVertices ( Vertex v, int edgetype ) {
	EdgeIterator edges = incidentEdges ( v, edgetype ); 
	return _adjacentVertices( v, edges );
    }

    /**
     * Built on incidentEdges(.)
     * <p>
     * O( min(v1.degree,v2.degree) )
     * @see InspectableGraph#areAdjacent(Vertex,Vertex)
     */
    public boolean areAdjacent(Vertex v1, Vertex v2) {
	if( degree(v1) < degree(v2) ) {
	    EdgeIterator edges = incidentEdges(v1);
	    while(edges.hasNext()) {
		if(opposite(v1, edges.nextEdge())==v2) return true;
	    }
	    return false;
	}
	else {
	    EdgeIterator edges = incidentEdges(v2);
	    while(edges.hasNext()) {
		if(opposite(v2, edges.nextEdge())==v1) return true;
	    }
	    return false;
	}
    }

    /**
     * Built on endVertices(.)
     * <p>
     * O(1)
     *
     * @see InspectableGraph#endVertices(Edge)
     */
    public boolean areAdjacent(Edge e1, Edge e2) {
	Vertex [] ev1 = endVertices(e1);
	Vertex [] ev2 = endVertices(e2);
	return ( ev1[0] == ev2[0] || ev1[0] == ev2[1] ||
		 ev1[1] == ev2[0] || ev1[1] == ev2[1] );
    }

    /**
     * Built on incidentEdges(.)
     * <p>
     * O( min(v1.degree,v2.degree) )
     *
     * @see InspectableGraph#incidentEdges(Vertex)
     */
    public EdgeIterator connectingEdges(Vertex v1, Vertex v2) {
	if( degree(v1) < degree(v2) ) {
	    EdgeIterator edges = incidentEdges(v1);
	    Sequence accum = new net.sourceforge.czt.jdsl.core.ref.NodeSequence();
	    while(edges.hasNext()) {
		Edge e = edges.nextEdge();
		if(opposite(v1,e) == v2) accum.insertLast(e);
	    }
	    return new EdgeIteratorAdapter( accum.elements() );
	}
	else {
	    EdgeIterator edges = incidentEdges(v2);
	    Sequence accum = new net.sourceforge.czt.jdsl.core.ref.NodeSequence();
	    while(edges.hasNext()) {
		Edge e = edges.nextEdge();
		if(opposite(v2,e) == v1) accum.insertLast(e);
	    }
	    return new EdgeIteratorAdapter( accum.elements() );
	}
    }

    /**
     * Built on incidentEdges(.)
     * <p>
     * O( min(v1.degree,v2.degree) )
     *
     * @see InspectableGraph#incidentEdges(Vertex)
     */
    public Edge aConnectingEdge( Vertex v1, Vertex v2 ) {
	if( degree(v1) < degree(v2) ) {
	    EdgeIterator edges = incidentEdges(v1);
	    while(edges.hasNext()) {
		Edge e = edges.nextEdge();
		if(opposite(v1,e) == v2) return e;
	    }
	    return Edge.NONE;
	}
	else {
	    EdgeIterator edges = incidentEdges(v2);
	    while(edges.hasNext()) {
		Edge e = edges.nextEdge();
		if(opposite(v2,e) == v1) return e;
	    }
	    return Edge.NONE;
	}
    }
    
    /**
     * Built on endVertices(.)
     * <p>
     * O(1)
     *
     * @see InspectableGraph#endVertices(Edge)
     */
    public Vertex aCommonVertex( Edge e1, Edge e2 ) {
	Vertex [] ev1 = endVertices(e1);
	Vertex [] ev2 = endVertices(e2);
	if (ev1[0] == ev2[0] || ev1[0] == ev2[1]) return ev1[0];
	if (ev1[1] == ev2[0] || ev1[1] == ev2[1]) return ev1[1];
	return Vertex.NONE;
    }




    // ---------------------------------------------------
    // private methods


    /**
     * Go through the list of edges and get the opposite of v along
     * that edge.
     * <p>
     * O(size of edgelist)
     *
     * @see InspectableGraph#opposite(Vertex,Edge)
     * @param v         The vertex
     * @param edgelist  The list of edges
     * @exception       InvalidPositionException if the vertex, or
     *                  edges in the edgelist are invalid or from the
     *                  wrong container
     * @return          The list of opposite vertices
     */
    private VertexIterator _adjacentVertices(Vertex v,
						 EdgeIterator edgelist) {
	Sequence accum = new net.sourceforge.czt.jdsl.core.ref.NodeSequence();
	Edge curr;
	while (edgelist.hasNext()) {
	    curr = edgelist.nextEdge();
	    accum.insertLast(opposite(v,curr));
	}
	return new VertexIteratorAdapter( accum.elements() );
    }


    

    // nested classes
  
    // class to mush two ObjectIterators into a single ObjectIterator
    protected static class OO_to_O_MergerIterator implements ObjectIterator {

	ObjectIterator o1_;
	ObjectIterator o2_;
	private int curr_; // 0, 1, or 2, for using o1_, o2_, or all finished
	
	// can't use currobj_==null, because null is a legit Object value:
	private boolean isStarted_; 
	private Object currobj_; // cache for answering the no-advance queries

	/** 
	 * Assumes neither iterator is null
	 */
        public OO_to_O_MergerIterator (ObjectIterator o1,
				       ObjectIterator o2) {
	    o1_ = o1;
	    o2_ = o2;
	    curr_ = 0;
	    isStarted_ = false;
	    currobj_ = null;
	}

	// note that hasNext() changes the internal state of the iterator,
	// though not in an externally visible way
	public boolean hasNext() {
	    if (curr_==0) {
		if ( o1_.hasNext() ) return true;
		else curr_ = 1;
	    }
	    if (curr_==1) {
		if ( o2_.hasNext() ) return true;
		else curr_ = 2;
	    }
	    assert curr_==2;
	    return false;
	}

	public Object nextObject() {
	    if ( ! hasNext() ) throw new java.util.NoSuchElementException
				   ( "No element remains." );
	    // curr_ has now been updated to an iterator that hasNext()
	    isStarted_ = true;
	    switch( curr_ ) {
	    case 0: return currobj_ = o1_.nextObject();
	    case 1: return currobj_ = o2_.nextObject(); 
	    default: assert false : "curr_ is neither 0 nor 1";
	    }
	    return null; // never reached because of asserting false
	}

	public Object object() {
	    if( isStarted_ == false ) throw new java.util.NoSuchElementException
				     ("iterator is before-the-first.");
	    return currobj_;
	}

	public void reset() {
	    o1_.reset();
	    o2_.reset();
	    curr_ = 0;
	    isStarted_ = false;
	    currobj_ = null;
	}

    } // class OO_to_O_MergerIterator


    // class to mash two PositionIterators into a single PositionIterator
    private static class PP_to_P_MergerIterator implements PositionIterator {

        PositionIterator p1_;
        PositionIterator p2_;
        private int curr_; // 0, 1, or 2, for using p1_, p2_, or all finished
        
        private Position currpos_; // cache for answering the no-advance queries

        PP_to_P_MergerIterator( PositionIterator p1, PositionIterator p2 ) {
	    assert p1 != null && p2 != null;
            p1_ = p1;
            p2_ = p2;
            curr_ = 0;
            currpos_ = null;
        }

        // note that hasNext() changes the internal state of the iterator,
        // though not in an externally visible way
        public boolean hasNext() {
            if (curr_==0) {
                if ( p1_.hasNext() ) return true;
                else curr_ = 1;
            }
            if (curr_==1) {
                if ( p2_.hasNext() ) return true;
                else curr_ = 2;
            }
            assert curr_==2;
            return false;
        }

        public Position nextPosition() {
            if ( ! hasNext() ) throw new java.util.NoSuchElementException
                                   ( "No element remains." );
            // curr_ has now been updated to an iterator that hasNext()
            switch( curr_ ) {
            case 0: return currpos_ = p1_.nextPosition();
            case 1: return currpos_ = p2_.nextPosition(); 
            default: assert false : "curr_ is neither 0 nor 1";
            }
            return null; // never reached because of asserting false
        }

        public Position position() {
            if( currpos_ == null ) throw new java.util.NoSuchElementException
                                     ("iterator is before-the-first.");
            return currpos_;
        }

	public Object element() {
	    return position().element();
	}

	// methods inherited from ObjectIterator interface
	public Object nextObject() { return nextPosition(); }
	public Object object() { return position(); }
	public void reset() {
	    p1_.reset();
	    p2_.reset();
	    curr_ = 0;
            currpos_ = null;
	}

    } // class PP_to_P_MergerIterator


}
