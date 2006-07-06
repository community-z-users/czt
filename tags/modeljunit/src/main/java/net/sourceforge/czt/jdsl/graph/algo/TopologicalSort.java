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
import net.sourceforge.czt.jdsl.core.api.PositionIterator;

/**
  * This algorithm class performs a topological ordering on a
  * given DAG. 
  *
  * Each Vertex is labeled with a unique order-number 
  * which may be retrieved using the number(Vertex) method.
  *
  * In addition to the number(Vertex) query method, this algo-object
  * provides a method sortedVertices(), for obtaining a VertexIterator
  * containing the Vertices in topologically sorted order.
  *
 * @author Lucy Perry (lep)
  *
  * @version JDSL 2.1.1 
  *
  * @see AbstractTopologicalSort
  */


public class TopologicalSort extends AbstractTopologicalSort {


  /**
    * This array will be used to create a VertexIterator on demand.
    * The array will be filled in during the execution of the algorithm.
    */
  private Vertex[] array_;


  /**
    * Constructor
    */
  public TopologicalSort(){
    super();
  }


  

 

  /**
    * The meat of the algorithm.
    * This method is called from the superclass's execute(.) method.
    * If the Graph is acyclic, then the algorithm labels each
    * Vertex with a unique topological order-number.
    * If the Graph contains cycles, then some Vertices will not be
    * visited, and the is_cyclic_ boolean will be set to true.
    * 
    * Takes O(V+E) time, where
    * V = number of Vertices in the Graph, and
    * E = number of Edges, 
    * because the algorithm traverses all the outgoing 
    * edges of each visited Vertex exactly once.
    */
  protected final void sort(){

    // This object will be the key for a key,value Decoration pair
    // It's used during execution to keep track of each Vertex's inDegree
    Object IN_DEG = new Object();
   
    VertexIterator verts = graph_.vertices();
    int numVerts = graph_.numVertices();
    Vertex v = null;

    // Label each Vertex w/ its inDegree
    while (verts.hasNext()){
      v = verts.nextVertex();
      int inDegree = graph_.degree(v, EdgeDirection.IN);
      v.set(IN_DEG, new Integer(inDegree));

      // Vertices are inserted into the queue only after all their 
      // predecessors have been dealt with.
      if (inDegree == 0){
	queue_.insertLast(v);
      }
    }
    
    // So we can build the VertexIterator later if needed
    array_ = new Vertex[numVerts];

    int topoNumber = 0;//start numbering vertices at 0

    while (!queue_.isEmpty()){
      v = (Vertex)queue_.removeFirst();
      v.set(NUMBER_KEY_, new Integer(topoNumber));
      
      //now add this Vertex to the array....
      array_[topoNumber] = v;

      topoNumber = topoNumber+1;//all the numbers are unique
      VertexIterator vi = graph_.adjacentVertices(v, EdgeDirection.OUT);
      while (vi.hasNext()){
	Vertex w = vi.nextVertex();
	int wInDegree = ((Integer)w.get(IN_DEG)).intValue() - 1;
	w.set(IN_DEG, new Integer(wInDegree));
	if (wInDegree == 0){//all its predecessors have been dealt with
	  queue_.insertLast(w);
	}
      }
    }

    //clean up some decorations
    verts.reset();
    while(verts.hasNext()){
      Vertex a = verts.nextVertex();
      a.destroy(IN_DEG);
    }


    //if some vertices have not been visited, then the graph has cycles
    if (topoNumber < numVerts){
      is_cyclic_ = true;
    }
    else{
      is_cyclic_ = false;
    }

  }

  
  /**
    * Returns a VertexIterator containing all the Vertices in topologically
    * sorted order.
    *
    * Takes O(1) time.
    *
    * @return VertexIterator
    * @exception InvalidQueryException if the Graph has cycles, or if
    * the algorithm has not yet been executed.
    */
  public VertexIterator sortedVertices() throws InvalidQueryException{
    if (is_cyclic_){
      throw new InvalidQueryException("Can't get sortedVertices "
				      + "on a cyclic graph");
    }
    else{
      PositionIterator pi = new net.sourceforge.czt.jdsl.core.ref.ArrayPositionIterator(array_);
      return new net.sourceforge.czt.jdsl.graph.ref.VertexIteratorAdapter(pi);
    }
  }


}
