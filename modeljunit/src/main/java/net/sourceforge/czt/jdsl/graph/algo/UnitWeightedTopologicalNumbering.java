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
  * This algorithm class computes the optimal unit-weighted topological 
  * numbering for a given DAG.
  *
  * Each Vertex is assigned a non-unique order-number.
  * The number of a given Vertex is equal to 1 plus the 
  * highest value of any of its predecessors' numbers.
  *
  * The order-number of a Vertex may be retrieved using the
  * number(Vertex) method.
  *
 * @author Natasha Gelfand (ng)
 * @author Lucy Perry (lep)
  *
  * @version JDSL 2.1.1 
  * @see AbstractTopologicalSort
  *

  */


public class UnitWeightedTopologicalNumbering extends AbstractTopologicalSort {


  /**
    * Constructor
    */
  public UnitWeightedTopologicalNumbering(){
    super();
  }




  /**
    * The meat of the algorithm.
    * This method is called from the superclass's execute(.) method.
    * If the Graph is acyclic, then the algorithm labels each
    * Vertex with a non-unique order-number.
    * If the Graph contains cycles, then some Vertices will not be visited,
    * and the is_cyclic_ boolean will be set to true.
    *
    * Takes O(V+E) time, where 
    * V = number of Vertices in the Graph, and
    * E = number of Edges,
    * because the algorithm traverses all the outgoing
    * edges of each visited Vertex exactly once.
    */
  protected final void sort(){
    is_cyclic_ = false;

    Object NUM_EXAMINED = new Object();
    Integer ZERO = new Integer(0);  // we use these a lot; might as well
    Integer NEG1 = new Integer(-1); // only have one instance

    VertexIterator verts = graph_.vertices();
    int numVerts = graph_.numVertices();
    
    Vertex v = null;

    //this loop takes care of initializing all the vertices
    while (verts.hasNext()){
      v = verts.nextVertex();

      // Initially, vertices have never been examined
      // (NUM_EXAMINED = the number of times the Vertex has been examined.)
      v.set(NUM_EXAMINED, ZERO);

      // Sources get a numbering of 0 and are inserted into the queue.
      // All others get the special value -1, which is less than the
      // smallest actual number.
      if (graph_.degree(v, EdgeDirection.IN) == 0){
	v.set(NUMBER_KEY_, ZERO);
	queue_.insertLast(v);
      }
      else{
	v.set(NUMBER_KEY_, NEG1);
      }
    }

    int numVisited = 0;//for use in determining if it has cycles

    //This loop sets the NUMBER_KEY_ of Vertices
    while (!queue_.isEmpty()){
      numVisited = numVisited+1;
      v = (Vertex)queue_.removeFirst();
      int v_number = _number(v);
      
      VertexIterator vi = graph_.adjacentVertices(v, EdgeDirection.OUT);
      while (vi.hasNext()){
	Vertex w = vi.nextVertex();
	int w_number = _number(w);
	//The NUMBER_KEY_ of a Vertex depends on the NUMBER_KEY_ of its predecessor
	if ((v_number+1) > w_number){
	  w.set(NUMBER_KEY_, new Integer(v_number+1));
	}
	int num_ex = ((Integer)w.get(NUM_EXAMINED)).intValue();
	w.set(NUM_EXAMINED, new Integer(num_ex+1));
	if (num_ex+1 == graph_.degree(w, EdgeDirection.IN)){
	  queue_.insertLast(w);
	}
      }
    }
    
    //clean up some decorations
    verts.reset();
    while(verts.hasNext()){
      Vertex a = verts.nextVertex();
      a.destroy(NUM_EXAMINED);
    }

    //if some vertices were never visited, then the graph has cycles
    if (numVisited < numVerts){
      is_cyclic_ = true;
    }
    
  }


  /*
    Private helper method which does the same thing as superclass's
    number(v) method, but which can be used internally by the algorithm
    without checking for is_cyclic_ (meaning that this method is 
    slightly faster.
  */
  private int _number(Vertex v){
    return ((Integer)v.get(NUMBER_KEY_)).intValue();
  }



}
