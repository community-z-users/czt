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
 * Empty, typing interface for <code>Position</code>s that are edges. 
 * All the functionality is in the <code>InspectableGraph</code> interface.
 *
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public interface Edge extends Position {

  /**
   * Used when a function requires an edge to be specified but
   * there is no edge to specify, or when a function needs to return
   * an edge but there is no edge to return.
   * @see InspectableGraph#anEdge()
   */
  // * @see jdsl.map.api.OrderedGraph#insertEdge
  public static final Edge NONE = new NONEEdge();


  // nested class(es)
  
  /** 
   * A dummy class, used to implement the constant
   * <code>Edge.NONE</code><br>.  Not intended for reuse
   * in any way.
   */
  static final class NONEEdge implements Edge {
	
    NONEEdge() { }
    
    public String toString() {
      return "Edge.NONE";
    }
    
    public Object element() throws InvalidAccessorException {
      throw new InvalidAccessorException("method called on Edge.NONE");
    }
    
    public void set (Object key, Object value) throws
      InvalidAccessorException {
      throw new InvalidAccessorException("method called on Edge.NONE");
    }
    
    public Object get (Object key) throws InvalidAccessorException {
      throw new InvalidAccessorException("method called on Edge.NONE");
    }
    
    public Object destroy (Object key) throws InvalidAccessorException {
      throw new InvalidAccessorException("method called on Edge.NONE");
    }
    
    public boolean has (Object key) throws InvalidAccessorException {
      throw new InvalidAccessorException("method called on Edge.NONE");
    }
    
    public ObjectIterator attributes () throws InvalidAccessorException {
      throw new InvalidAccessorException("method called on Edge.NONE");
    }
    
  }
 
}
