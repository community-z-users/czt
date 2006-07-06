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



/**
 * This is an exception thrown specifically by the DFS to signify that
 * an internal error has arisen in the computation of start/finish
 * times.
 *
 * AnachronismExceptions can now take a "cause" to enhance the stack trace.
 * This should be used if a low-level exception was caught, but could not be
 * resolved -- so a higher-level exception (this) was thrown. The cause of an
 * exception can be any throwable object.
 *
 * @author David Ellis
 * @author based on a previous version by Keith Schmidt
 * @version JDSL 2.1.1 
 * @see Throwable
 */
public class AnachronismException extends RuntimeException {

  /** 
   * A constructor that takes a String that (hopefully) contains a
   * relevant message about the circumstances under which this
   * exception was thrown.
   */
  public AnachronismException(String msg) {
    super(msg);
  }
  
  public AnachronismException (String message, Throwable cause) {
	  super(message, cause);
  }
   
  public AnachronismException (Throwable cause) {
	  super(cause);
  }

}
