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

package net.sourceforge.czt.jdsl.graph.ref ;

import net.sourceforge.czt.jdsl.core.api.*;
import net.sourceforge.czt.jdsl.core.ref.NodeSequence;
import net.sourceforge.czt.jdsl.graph.api.*;



/**
 * An implementation of the Graph interface, including self-loops,
 * parallel edges, and mixed directed and undirected edges.  For
 * specifications of the methods, see the documentation of
 * the interfaces. The remainder of this description is about the
 * implementation.  
 * <p>
 *
 * The following is a high-level description of the design; low-level
 * details appear further below.  The graph is implemented via a list of
 * vertices and a list of edges.  The nodes of these "global" lists are the
 * vertices and edges of the graph, respectively. In addition to the
 * global lists of vertices and edges, each vertex has a "local" list of
 * its incident edges.  Thus, each edge participates
 * in two local lists (one for each endpoint) plus the global list.  Each
 * vertex participates in only the global list.  Although sequential
 * data structures are used to implement the graph, the graph
 * conceptually consists of unordered sets; no guarantee is made
 * about where in the various lists a given accessor appears.
 * <p>
 *
 * This design forces most of the methods' time complexities.  Insertion
 * and deletion of vertices and edges are constant-time because
 * the various doubly-linked lists can be modified in constant time.
 * Adjacency queries are typically O(degrees of vertices involved).
 * Iterations take time linear in the number of things iterated over.
 * <p>
 * 
 * The remainder of this description is about low-level details
 * of the design, and efficiency tradeoffs of alternate designs.
 * <p>
 * 
 * The global list of edges exists to avoid having the duplicates in
 * edges() that would result from asking all vertices for their incident
 * edges (each edge would appear twice).  For most other purposes, the
 * only global list required would be the vertex list.  An alternate
 * design would get rid of the global edge list and would do a
 * traversal to get edges().  This would save space at the cost of
 * increasing the complexity of edges() from O(E) to O(V+E).
 * <p>
 *
 * Both global lists are implemented with JDSL NodeSequences.  In
 * contrast, the local incidence lists at each vertex are implemented
 * "by hand," with links in the ILEdges, for space efficiency.
 * Internal methods that refer to those links also take a vertex, so
 * the edge knows which set of links is being referred to (the set for
 * one endpoint or the set for the other endpoint).  Each local list
 * includes a dummy edge to handle special cases (empty list,
 * iterating till end of list, inserting at beginning of list).
 * <p>
 * 
 * To avoid the space overhead of having the global lists' positions
 * point to vertex/edge objects, which would need to point back to
 * the positions, the positions *are* the vertices/edges.
 * This is accomplished by inheriting from the position implementation
 * of the NodeSequence (called FNSNode) and using the
 * posInsert* methods to put objects of the subclass
 * into the global lists.
 * <p>
 * 
 * Research issues.  The following are changes to the design that
 * could be made if experiments indicated they were worthwhile:
 * <ul>
 *   <li>Use caches and copy-on-write techniques in more methods
 *       that return iterators.  However, many graph algorithms
 *       iterate over a given set only once, so caching the iteration
 *       might just waste time and space.  It might also be
 *       difficult to determine when to invalidate a cache.
 *   <li>Use dictionaries to store some information, for example the
 *       adjacency lists, in order to have better running-time for
 *       adjacency queries -- for example, connectingEdges(V,V).  This 
 *       would improve asymptotic performance of adjacency queries
 *       at the expense of asymptotic penalties in modifications,
 *       and at the expense of constant-factor penalties everywhere.
 *   <li>Have vertices store 3 lists of edges, incoming, outgoing, and
 *       undirected, for faster iterations over categories of edges.
 *       However, this gives space overhead, and is faster only
 *       in the rare case of a graph with both directed and undirected edges.
 * </ul>
 *
 * @see Graph
 * @see Vertex
 * @see Edge
 * @see EdgeDirection
 *
 * @author Benoit Hudson
 * @author Mark Handy
 *
 * @version JDSL 2.1.1 
 */

public class IncidenceListGraph extends AbstractGraph
implements Graph, EdgeDirection {

    private NodeSequence allverts_ ;
    private NodeSequence alledges_ ;


    /**
     * Creates a new IncidenceListGraph with default parameters.
     * <p>
     * O(1)
     */
    public IncidenceListGraph() {
        super();
        allverts_ = new NodeSequence();
        alledges_ = new NodeSequence();
    }





    /************ [Positional] Container ***************/


    /**
     * O(1)
     */
    public Container newContainer() {
        return new IncidenceListGraph();
    }

    /**
     * O(1)
     */
    public Object replaceElement( Accessor p, Object newElement ) {
	if( allverts_.contains(p) ) return ( (ILVertex)p ).replaceElement( newElement );
	if( alledges_.contains(p) ) return ( (ILEdge)p ).replaceElement( newElement );
	throw new InvalidAccessorException( "Accessor not contained: " + p );
    }

    /** 
     * O(1) 
     */
     public boolean contains( Accessor p ) {
	return allverts_.contains(p) || alledges_.contains(p);
     }

    /**
     * O(V+E)
     */
    public ObjectIterator elements() {
	return new OO_to_O_MergerIterator(
					  allverts_.elements(),
					  alledges_.elements()
					  );
    }



    /************ InspectableGraph ***************/
    
    /**
     * O(1)
     */
    public int numVertices() {
        return allverts_.size() ;
    }

    /**
     * O(1)
     */
    public int numEdges() {
        return alledges_.size() ;
    }

    /**
     * O(V)
     */
    public VertexIterator vertices() {
	return new VertexIteratorAdapter( allverts_.positions() );
    }

    /**
      * O(1)
      */
    public Vertex aVertex() {
	if (allverts_.isEmpty()) return Vertex.NONE;
	return (Vertex)allverts_.first();
    }

    /**
     * O(E)
     */
    public EdgeIterator edges() {
	return new EdgeIteratorAdapter( alledges_.positions() );
    }
    
    /**
     * O(1)
     */
    public Edge anEdge() {
	if (alledges_.isEmpty()) return Edge.NONE;
	return (Edge)alledges_.first();
    }

    
    
    /**
     * O(1)
     */
    public int degree (Vertex v) throws InvalidAccessorException {
        return _checkVertex(v).degree();
    }

    /**
     * O(degree)
     */
    public int degree( Vertex v, int edgetype ) throws InvalidAccessorException {
	return _checkVertex(v).degree( edgetype );
    }
	
    
    /**
     * O(degree)
     */
    public EdgeIterator incidentEdges (Vertex v) throws
    InvalidAccessorException {
	return _checkVertex(v).incidentEdges( IN | OUT | UNDIR );
    }
    
    /**
     * O(degree)
     */
    public EdgeIterator incidentEdges( Vertex v, int edgetype ) throws
    InvalidAccessorException {
	return _checkVertex(v).incidentEdges( edgetype );
    }
    
    /**
     * O(1)
     */
    public Edge anIncidentEdge (Vertex v) throws InvalidAccessorException {
        Edge retval = _checkVertex(v).anEdge( IN | OUT | UNDIR );
	if( retval==null ) retval = Edge.NONE;
	return retval;
    }
    
    /**
     * O(degree)
     */
    public Edge anIncidentEdge( Vertex v, int edgetype ) throws 
    InvalidAccessorException {
	Edge retval = _checkVertex(v).anEdge( edgetype );
	if( retval==null ) retval = Edge.NONE;
	return retval;
    }


    /**  
     * O(1)
     */
    public Vertex[] endVertices (Edge e) {
        return _checkEdge(e).endpoints();
    }
    
    /** 
     * O(1)
     */
    public boolean areIncident(Vertex v, Edge e) {
	_checkVertex(v);
	Vertex [] ev = endVertices(e);
	return (ev[0] == v || ev[1] == v);
    }

    /** 
     * O(1)
     */
    public Vertex opposite (Vertex v, Edge e) {
	_checkVertex(v);
	Vertex[] ends = endVertices(e);
	if( ends[0]==v ) return ends[1];
	if( ends[1]==v ) return ends[0];
	throw new InvalidVertexException( "v not an endpoint of e" );
    }

    /**
     * O(1)
     */
    public Vertex origin(Edge e) {
	if(!isDirected(e))
	    throw new InvalidEdgeException("Undirected edge:\n"+ e);
	else
	    return endVertices(e)[0];
    }

    /**
     * O(1)
     */
    public Vertex destination(Edge e) {
	if(!isDirected(e))
	    throw new InvalidEdgeException("Undirected edge:\n"+ e);
	else
	    return endVertices(e)[1];
    }




    
    /*************** [Modifiable] Graph ******************/
    
    
    /**
     * O(1)
     */
    public Vertex insertVertex(Object elt) {
	return _insertVertex( elt );
    }

    /**
     * O(degree)
     */
    public Object removeVertex(Vertex v) throws InvalidAccessorException {
        _removeVertex( _checkVertex(v) );
	return v.element();
    }


    

    /**
     * O(1)
     */
    public Edge attachVertex(Vertex v, Object vertexInfo, Object edgeInfo)
    throws InvalidAccessorException {
	ILVertex ilv = _checkVertex(v);
        ILVertex newv = _insertVertex( vertexInfo );
        return _insertEdge( ilv, newv, edgeInfo, false );
    }

    /**
     * O(1)
     */
    public Edge attachVertexFrom(Vertex v, Object vertexInfo, Object edgeInfo)
    throws InvalidAccessorException {
	ILVertex ilv = _checkVertex(v);
        ILVertex newv = _insertVertex( vertexInfo );
        return _insertEdge( ilv, newv, edgeInfo, true);
    }

    /**
     * O(1)
     */
    public Edge attachVertexTo(Vertex v, Object vertexInfo, Object edgeInfo)
    throws InvalidAccessorException {
	ILVertex ilv = _checkVertex(v);
        ILVertex newv = _insertVertex( vertexInfo );
        return _insertEdge( newv, ilv, edgeInfo, true);
    }



    
    /**
     * O(1)
     */
    public Edge insertEdge (Vertex v1, Vertex v2, Object elt) throws
    InvalidAccessorException {
	ILVertex ilv1 = _checkVertex(v1);
	ILVertex ilv2 = _checkVertex(v2);
        return _insertEdge( ilv1, ilv2, elt, false);
    }

    /**
     * O(1)
     */
    public Edge insertDirectedEdge (Vertex v1, Vertex v2, Object elt) throws
    InvalidAccessorException {
	ILVertex ilv1 = _checkVertex(v1);
	ILVertex ilv2 = _checkVertex(v2);
        return _insertEdge( ilv1, ilv2, elt, true);
    }

    /**
     * O(1)
     */
    public Object removeEdge (Edge e) throws InvalidAccessorException {
        ILEdge edge = _checkEdge(e);
        _removeEdge(edge);
	return e.element();
    }




   /**
     * O(1)
     */
    public Vertex splitEdge(Edge e, Object elt) throws
    InvalidAccessorException {
	ILEdge ile = _checkEdge(e);

        // create the new midpoint
        ILVertex newv = _insertVertex(elt);

	// useful info about old edge
	boolean isDir = ile.isDir();
        ILVertex[] endpts = ile.endpoints();

        // insert new edges between endpoints and new midpoint
        _insertEdge( endpts[0], newv, null, isDir );
        _insertEdge( newv, endpts[1], null, isDir );

        // remove old edge, return new vertex
        _removeEdge(ile);
        return newv ;
    }


    /**
     * Note: the "two" edges incident on v cannot be the same edge.  That is, v
     * is technically of degree 2 if it has a single self-loop and is
     * otherwise isolated, but it is impossible to unsplit that
     * edge-vertex-edge combination, so we throw IVE in that case.
     * <p>
     * O(1)
     */
    public Edge unsplitEdge (Vertex v, Object o) throws
    InvalidAccessorException, InvalidVertexException {
        ILVertex ilv = _checkVertex(v);
	
	// make sure v's degree is right
	if(ilv.degree()!=2) throw new InvalidVertexException
				("trying to unsplitEdge on vertex of degree " + ilv.degree());
	
	// get the 2 edges and 2 vertices associated with v
	EdgeIterator edges = incidentEdges(v);
	Edge e1 = edges.nextEdge();
	Edge e2 = edges.nextEdge();
	assert !edges.hasNext()
	  : "v of degree 2 has more than 2 incidentEdges()";
	// make sure this isn't a lone vertex with a self-loop
	if (e1==e2) throw new InvalidVertexException
			("trying to unsplitEdge on a vertex with only a self-loop");
	Vertex v1 = opposite(v, e1);
	Vertex v2 = opposite(v, e2);
	
	// decide whether to direct the new edge (and if so, make sure
	// v1 is the origin of the new edge, swapping v1 and v2 if necessary).
	boolean isdirected = false;
	if( isDirected(e1) && isDirected(e2) ) { 
	    if( origin(e1)==origin(e2) || destination(e1)==destination(e2) ) {
		// the edges are inconsistently directed
		isdirected = false;
	    }
	    else {
		isdirected = true;
		if( destination(e1)==v1 ) {
		    // swap the points for the call to insertDirectedEdge(.)
		    Vertex vtemp = v1 ;
		    v1 = v2 ;
		    v2 = vtemp ;
		}
	    }
	}
	// else isdirected==false because e1 or e2 is undirected    
	
	// remove the old vertex and incident edges, and add an edge
	_removeVertex(ilv);
	return _insertEdge( (ILVertex)v1, (ILVertex)v2, o, isdirected);
    }
    

    
    
    /**
     * O(1)
     */
    public boolean isDirected(Edge e) {
        return _checkEdge(e).isDir();
    }

    /**
     * O(1)
     */
    public void setDirectionFrom(Edge e, Vertex v) {
	_checkVertex(v);
        _checkEdge(e).setDirectionFrom(v);
    }

    /**
     * O(1)
     */
    public void setDirectionTo(Edge e, Vertex v) {
	_checkVertex(v);
        _checkEdge(e).setDirectionTo(v);
    }

    /**
     * O(1)
     */
    public void makeUndirected(Edge e) {
        _checkEdge(e).makeUndirected();
    }

    /**
     * O(1)
     */
    public void reverseDirection(Edge e) {
	ILEdge ile = _checkEdge(e);
        if( ile.isDir() )  ile.swapEndpoints();
        else throw new InvalidEdgeException("trying to reverse undirected edge");
    }



    public String toString() {
	return net.sourceforge.czt.jdsl.graph.ref.ToString.stringfor(this);
    }




    

    /*********************** private helper methods ********************/

    

    

    // O(1)
    private ILVertex _insertVertex( Object elt ) {
	ILVertex vert = new ILVertex( elt );
        allverts_.posInsertLast( vert );
        return vert;
    }

    // O(1)
    private ILEdge _insertEdge( ILVertex v1, ILVertex v2, Object elt, boolean isDir) {
        ILEdge ile;
	if( v1==v2 ) ile = new ILLoopEdge( v1, elt, isDir );
	else ile = new ILNormalEdge( v1, v2, elt, isDir );
        alledges_.posInsertLast( ile );
        return ile ;
    }

    // O(degree)
    // overhead of multiple casts could be avoided by moving this
    // functionality to ILVertex
    private void _removeVertex( ILVertex vert ) {
        EdgeIterator pe = vert.incidentEdges( IN | OUT | UNDIR );
        while(pe.hasNext()) {
	    // strange-seeming containment check to guard against removing
	    // a self-loop twice:
	    if( alledges_.contains(pe.nextEdge()) ) _removeEdge( (ILEdge)pe.edge() );
	}
        allverts_.remove(vert);
    }

    // O(1)
    private void _removeEdge(ILEdge edge) {
	edge.detach();
        alledges_.remove(edge);
    }	

    // make sure vertex is valid, and cast it to implementation type
    private ILVertex _checkVertex( Vertex v ) {
	if( v==null ) throw new InvalidAccessorException
			  ( "vertex is null" );
	if( ! (v instanceof ILVertex) ) throw new InvalidAccessorException
					  ("invalid vertex class (" + v.getClass() + ")");
	if( ! allverts_.contains(v) ) throw new InvalidAccessorException
						   ("vertex belongs to a different graph");
	return (ILVertex)v;
    }

    // make sure edge is valid, and cast it to implementation type
    private ILEdge _checkEdge( Edge e ) {
	if( e==null ) throw new InvalidAccessorException
			  ( "edge is null" );
	if( ! (e instanceof ILEdge) ) throw new InvalidAccessorException
					  ("invalid edge class (" + e.getClass() + ")");
	if( ! alledges_.contains(e) ) throw new InvalidAccessorException
						   ("edge belongs to a different graph");
	return (ILEdge)e;
    }



    

    

    // ===============================================
    // nested classes
    


    /**
     * Dummy node in each vertex's list of edges, so the vertex and
     * the real edges 
     * always have something to point to (avoids special-casing on
     * ends of edge list and on detached vertices).  The interesting
     * methods take vertices (ignored by the dummy) because
     * real edges have two endpoints, so they need to know
     * which endpoint's list is being talked about.
     */
    private static class ILEdgeDummy extends ILEdge {
	private ILEdge next_, prev_;
	
	ILEdgeDummy() { next_ = prev_ = this; }
	ILEdge next() { return next_; }
	ILEdge next( Vertex whichEnd ) { return next_; }
	ILEdge prev( Vertex whichEnd ) { return prev_; }
	void setNext( Vertex whichEnd, ILEdge n ) { next_ = n; }
	void setPrev( Vertex whichEnd, ILEdge n ) { prev_ = n; }
	public String toString() { return "dummy edge!  you should never see this!"; }
	
	// using any other method indicates a bug:
	
	boolean isDir() {
	    assert false : "trying to use dummy node";
	    return false; }
        void makeDirected() {
	  assert false : "trying to use dummy node";
	}
        void makeUndirected() {
	  assert false : "trying to use dummy node";
	}
	boolean isSelfLoop() {
	    assert false : "trying to use dummy node";
	    return false; }
	ILVertex[] endpoints() {
	    assert false : "trying to use dummy node";
	    return null; }
	ILVertex origin() {
	    assert false : "trying to use dummy node";
	    return null;  }
	ILVertex destination() {
	    assert false : "trying to use dummy node";
	    return null;  }
        void setDirectionFrom(Vertex v) {
	  assert false : "trying to use dummy node";
	}
        void setDirectionTo(Vertex v) {
	  assert false : "trying to use dummy node";
	}
        void swapEndpoints() {
	  assert false : "trying to use dummy node";
	}
	int edgetype(Vertex v) {
	    assert false : "trying to use dummy node"; 
	    return -1; }
	int numMatches( Vertex v, int edgetype ) {
	    assert false : "trying to use dummy node";
	    return -1; }
        void detach() {
	  assert false : "trying to remove dummy node from e-list";
	}
    }


    
    /**
     * Vertices of <code>IncidenceListGraph</code>.  The inheritance
     * from FNSNode works the magic by which a vertex is also
     * a position in the global vertex list.  The vertex keeps a circularly
     * linked list of its incident edges.  The edges themselves contain
     * the links that implement the list (and since each edge has two
     * endpoints, it must have two sets of links).  The vertex starts
     * out with a dummy edge in order to avoid special-casing on
     * empty lists and ends of lists.
     *
     * @see IncidenceListGraph
     */
    private static class ILVertex extends net.sourceforge.czt.jdsl.core.ref.NodeSequence.FNSNode
    implements Vertex {

	// vert holds circularly linked list of edges, with one dummy node
	// always present
	private ILEdgeDummy edummy_;
	private int size_;


        /**
         * Create a new isolated vertex.
         *
         * @param elt   The element associated with this position
         */
        ILVertex( Object elt ) {
            super( elt );
	    edummy_ = new ILEdgeDummy();
	    size_ = 0;
        }


	Object replaceElement( Object newElement ) {
	    Object retval = element();
	    setElement( newElement );
	    return retval;
	}


	// used by a newly inserted edge to install itself in
	// its endpoints' incidence lists:
	ILEdgeDummy dummy() { return edummy_; }

	// an edge, when being added or removed, notifies its
	// endpoints of the arrival/departure:
	void loseEdge( ILEdge e ) { --size_; }
	void gainEdge( ILEdge e ) { ++size_; }

	
        /**
         * O(1).  Self-loops reported twice.
         *
         * @return  The degree (in, out, and undirected).
         */
        int degree() { return size_; }

	/** 
	 * O(degree).  Self-loops reported twice unless they are directed
	 * and only one direction is requested.
	 * @param edgetype
	 */
 	int degree( int edgetype ) {
	    int retval = 0;
	    ILEdge e = edummy_.next();
	    while( e != edummy_ ) {
		retval += e.numMatches( this, edgetype );
		/*
		  if( (e.edgetype(this) & edgetype) != 0 ) {
		  ++retval;
		  if( e.isSelfLoop() &&
		  edgetype != IN &&
		  edgetype != OUT ) ++retval;
		  }
		  */
		e = e.next( this );
	    }
	    return retval;
	}


        /**
         * Get an iterator of all edges incident to this vertex that are of
	 * the specified type relative to this vertex (incoming, etc.).
         * A self-loop is reported twice, unless the self-loop is directed
	 * and only one direction is requested.
         *
	 * @param edgetype a constant, or an OR of constants, from
	 * the EdgeDirection interface
         * @return  All incident edges (in, out, and undirected)
         */
        EdgeIterator incidentEdges( int edgetype ) {
	    Sequence accum = new net.sourceforge.czt.jdsl.core.ref.NodeSequence();
	    ILEdge e = edummy_.next();
	    while( e != edummy_ ) {
		int num = e.numMatches( this, edgetype );
		// num is 0, 1, or 2
		if( num>0 ) accum.insertLast(e);
		if( num>1 ) accum.insertLast(e);
		/*
		  if( (e.edgetype(this) & edgetype) != 0 ) {
		  accum.insertLast( e );
		  if( e.isSelfLoop() &&
		  edgetype != IN &&
		  edgetype != OUT ) accum.insertLast( e );
		  }
		  */
		e = e.next( this );
	    }
	    return new EdgeIteratorAdapter( accum.elements() );
	}

	
        /**
         * Get an incident edge of the specified type.  Takes O(degree)
	 * time unless the specified type is the OR of all types, in which
	 * case, constant-time.
         *
         * @return An incident edge (in, out, or undirected), or Edge.NONE
         */
        ILEdge anEdge( int edgetype ) {
	    ILEdge e = edummy_.next();
	    while( e != edummy_ ) {
		if( e.numMatches( this, edgetype ) > 0 ) return e;
		e = e.next( this );
	    }
	    return null;
        }

	public String toString() {
	    return net.sourceforge.czt.jdsl.graph.ref.ToString.stringfor(this);
	}

    } // class ILVertex




    /**
     * Abstract superclass of all edges, basically providing an
     * interface that edges have to meet, plus element- and direction-
     * related services.  This class is here basically to
     * prevent having data members where they are not needed.
     * The inheritance from FNSNode works the magic by which an edge
     * is also a position in the global edge list.
     */
  private static abstract class ILEdge
    extends net.sourceforge.czt.jdsl.core.ref.NodeSequence.FNSNode implements Edge {

	private boolean isDirected_;

	ILEdge() { super( null ); } // to be used only by ILEdgeDummy
	ILEdge( Object elt, boolean isDir ) {
	    super( elt );
	    isDirected_ = isDir;
	}

	Object replaceElement( Object newElement ) {
	    Object retval = super.element();
	    super.setElement( newElement );
	    return retval;
	}

	public String toString() {
	    return net.sourceforge.czt.jdsl.graph.ref.ToString.stringfor(this);
	}

	// an edge, when being removed, removes itself from
	// its endpoints' incidence lists
	abstract void detach();

	// methods dealing with the edge's place in its endpoints'
	// incidence lists.  They take a vertex to specify which
	// endpoint.
 	abstract ILEdge next( Vertex whichEnd );
	abstract ILEdge prev( Vertex whichEnd );
	abstract void setNext( Vertex whichEnd, ILEdge e );
	abstract void setPrev( Vertex whichEnd, ILEdge e );

	// methods dealing with endpoints
	abstract boolean isSelfLoop();
	abstract ILVertex[] endpoints(); // if directed, origin is first
	abstract void swapEndpoints(); // if directed, reverses direction

	// methods dealing with directedness
        boolean isDir() { return isDirected_; }
        void makeDirected() { isDirected_ = true; }
	void makeUndirected() { isDirected_ = false; }
	abstract ILVertex origin();
	abstract ILVertex destination();
	abstract void setDirectionFrom( Vertex v );
	abstract void setDirectionTo( Vertex v );

	// tells whether this edge is undirected, incoming, or outgoing
	// relative to the vertex specified
	abstract int edgetype( Vertex endpoint ); // now unused
	abstract int numMatches( Vertex endpt, int edgetype );
	
    }

	

    /**
     * Edges that have two distinct endpoints.  See ILEdge
     * for specifications of methods.
     *
     * @see IncidenceListGraph
     * @see IncidenceListGraph.ILEdge
     */
    private static class ILNormalEdge extends ILEdge {
	
	// endpoints: if directed, v1 is origin, v2 dest
        private ILVertex v1_, v2_ ;
	// links in the edge lists of the two endpoints:
        private ILEdge prev1_, next1_, prev2_, next2_;

	// every edge constructed knows its endpoints, and installs itself 
	// in its endpoints' incidence lists.
        ILNormalEdge( ILVertex v1, ILVertex v2,
	       Object elt, boolean isDirected) {
            super( elt, isDirected );

	    assert v1 != v2;
            v1_ = v1;
	    v2_ = v2;

	    // link self into one endpoint's edge list:
	    prev1_ = v1.dummy();
	    next1_ = v1.dummy().next();
	    prev1_.setNext( v1, this );
	    next1_.setPrev( v1, this );
	    // notify endpoint of new arrival:
	    v1.gainEdge( this ); 

	    // symmetric code for other endpoint:
	    prev2_ = v2.dummy();
	    next2_ = v2.dummy().next();
	    prev2_.setNext( v2, this );
	    next2_.setPrev( v2, this );
	    v2.gainEdge( this );
	    
        }

	
	void detach() {

	    // unlink self from endpoints' edge lists:
	    prev1_.setNext( v1_, next1_ );
	    next1_.setPrev( v1_, prev1_ );
	    prev2_.setNext( v2_, next2_ );
	    next2_.setPrev( v2_, prev2_ );

	    // notify endpoints of the edge's departure:
	    v1_.loseEdge( this );
	    v2_.loseEdge( this );
	    
	    // encourage explosions if a bug happens:
	    prev1_ = next1_ = prev2_ = next2_ = null;
	    v1_ = v2_ = null; 

	}

	
	
	ILEdge next( Vertex whichEnd ) {
	    if( v1_==whichEnd ) return next1_;
	    assert v2_==whichEnd;
	    return next2_;
	}

	ILEdge prev( Vertex whichEnd ) {
	    if( v1_==whichEnd ) return prev1_;
	    assert v2_==whichEnd;
	    return prev2_;
	}

	void setNext( Vertex whichEnd, ILEdge n ) {
	    if( v1_==whichEnd ) next1_ = n;
	    else {
		assert v2_==whichEnd;
		next2_ = n;
	    }
	}

	void setPrev( Vertex whichEnd, ILEdge n ) {
	    if( v1_==whichEnd ) prev1_ = n;
	    else {
		assert v2_==whichEnd;
		prev2_ = n;
	    }
	}

	

        boolean isSelfLoop() { return false; }
	
        ILVertex[] endpoints() {
            ILVertex[] retval = new ILVertex[2];
            retval[0] = v1_;
            retval[1] = v2_;
            return retval;
        }

        void swapEndpoints() {
            ILVertex vtemp = v1_ ;
            v1_ = v2_ ;
            v2_ = vtemp;

            ILEdge etemp = next1_;
	    next1_ = next2_;
	    next2_ = etemp;

	    etemp = prev1_;
	    prev1_ = prev2_;
	    prev2_ = etemp;
        }


	
        ILVertex origin() {
            assert isDir();
            return v1_;
        }
	
        ILVertex destination() {
            assert isDir();
            return v2_;
        }

        void setDirectionFrom(Vertex v) {
            makeDirected();
            if(v==v1_) return;
            if(v==v2_) swapEndpoints();
	    else throw new InvalidVertexException( "Vertex " + v +
						  " not an endpoint of edge " + this );
        }

        void setDirectionTo(Vertex v) {
            makeDirected();
            if(v==v2_) return;
	    if(v==v1_) swapEndpoints();
	    else throw new InvalidVertexException( "Vertex " + v +
						  " not an endpoint of edge " + this );
        }



	int edgetype( Vertex endpoint ) {
	    if( isDir() ) {
		if( endpoint==v1_ ) return EdgeDirection.OUT;
		assert endpoint==v2_ : "not an endpoint";
		return EdgeDirection.IN;
	    }
	    else {
	        assert endpoint==v1_ || endpoint==v2_ : "not an endpoint";
		return EdgeDirection.UNDIR;
	    }
	}

	int numMatches( Vertex endpt, int edgetype ) {
	    int mytype = edgetype( endpt );
	    if( (mytype & edgetype) != 0 ) return 1;
	    else return 0;
	}


    } // class ILNormalEdge


    private static class ILLoopEdge extends ILEdge {

	private ILVertex v_; // has only one endpoint
	private ILEdge prev_, next_;

	ILLoopEdge( ILVertex v, Object elt, boolean isDirected ) {
	    super( elt, isDirected );
	    v_ = v;
	    prev_ = v.dummy();
	    next_ = v.dummy().next();
	    prev_.setNext( v, this );
	    next_.setPrev( v, this );
	    v.gainEdge( this );
	    v.gainEdge( this ); // fool v into thinking this is two edges
	}

	void detach() {
	    prev_.setNext( v_, next_ );
	    next_.setPrev( v_, prev_ );
	    v_.loseEdge( this );
	    v_.loseEdge( this ); // maintain illusion established in ctor
	    prev_ = next_ = null; // make this object useless
	    v_ = null;
	}

	

	ILEdge next( Vertex whichEnd ) {
	    assert whichEnd == v_;
	    return next_;
	}

	ILEdge prev( Vertex whichEnd ) {
	    assert whichEnd == v_;
	    return prev_;
	}

	void setNext( Vertex whichEnd, ILEdge e ) {
	    assert whichEnd == v_;
	    next_ = e;
	}

    	void setPrev( Vertex whichEnd, ILEdge e ) {
	    assert whichEnd == v_;
	    prev_ = e;
	}


	boolean isSelfLoop() { return true; }

	ILVertex[] endpoints() {
            ILVertex[] retval = new ILVertex[2];
            retval[0] = v_;
            retval[1] = v_;
            return retval;
        }

	void swapEndpoints() { }


	ILVertex origin() {
            assert isDir();
            return v_;
        }
	
        ILVertex destination() {
            assert isDir();
            return v_;
        }

	void setDirectionFrom( Vertex v ) {
	    makeDirected();
	    if( v != v_ )  throw new InvalidVertexException( "Vertex " + v +
							     " not an endpoint of edge " + this );
	}

	void setDirectionTo( Vertex v ) {
	    makeDirected();
	    if( v != v_ )  throw new InvalidVertexException( "Vertex " + v +
							     " not an endpoint of edge " + this );
	}


	int edgetype( Vertex endpoint ) {
	    // self-loops are both incoming and outgoing !
	    if( isDir() ) return EdgeDirection.IN | EdgeDirection.OUT;
	    else return EdgeDirection.UNDIR;
	}

	int numMatches( Vertex endpt, int edgetype ) {
	    assert endpt==v_;
	    if( isDir() ) {
		int retval = 0;
		if( (EdgeDirection. IN & edgetype) != 0 ) ++retval;
		if( (EdgeDirection.OUT & edgetype) != 0 ) ++retval;
		return retval;
	    }
	    else {
		if( (EdgeDirection.UNDIR & edgetype) != 0 ) return 2;
		else return 0;
	    }
	}


    } // ILLoopEdge


}
