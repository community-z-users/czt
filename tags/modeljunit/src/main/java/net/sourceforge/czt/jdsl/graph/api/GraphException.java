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

import java.lang.RuntimeException;



/** 
  * <code>net.sourceforge.czt.jdsl.graph.api</code> package. 
  * Not intended ever to be instantiated directly.
  *
  * GraphExceptions (and its subclasses) can now take a "cause" to enhance
  * the stack trace. This should be used if a low-level exception was caught,
  * but could not be resolved -- so a higher-level exception (this) was thrown.
  * The cause of an exception can be any throwable object.
  *
 * @author David Ellis
 * @author based on a previous version by Benoit Hudson
  * @version JDSL 2.1.1 
  * @see Throwable
  */
public class GraphException extends RuntimeException {

  public GraphException (String message) {
    super(message);
  }

  public GraphException (String message, Throwable cause) {
	  super(message, cause);
  }
   
  public GraphException (Throwable cause) {
	  super(cause);
  }

}
