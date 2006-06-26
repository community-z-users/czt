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



/**
 * An object of this class gets thrown when topological information related
 * to vertices is incorrect.  Note that this
 * exception is not intended to replace the
 * <code>net.sourceforge.czt.jdsl.core.api.InvalidAccessorException</code>, 
 * which covers cases where the vertex passed to a function is null, or
 * of a different implementation class, or from a different container.
 * 
 * For example, an <code>InvalidVertexException</code> is thrown
 * from <code>InspectableGraph.opposite(v,e)</code> when
 * <code>v</code> is not an endpoint of <code>e</code>.
 *
 * @author David Ellis
 * @author based on a previous version by Benoit Hudson
 * @version JDSL 2.1.1 
 * @see Vertex
 */
public class InvalidVertexException extends GraphException {

  public InvalidVertexException (String message) {
    super(message);
  }

  public InvalidVertexException (String message, Throwable cause) {
	  super(message, cause);
  }
   
  public InvalidVertexException (Throwable cause) {
	  super(cause);
  }

}
