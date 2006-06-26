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

package net.sourceforge.czt.jdsl.core.api;



/** 
 * This is the class from which all exceptions of the core package are
 * descended.<p>
 * 
 * CoreExceptions (and its subclasses) can now take a "cause" to enhance the
 * stack trace. This should be used if a low-level exception was caught, but
 * could not be resolved -- so a higher-level exception (this) was thrown.
 * The cause of an exception can be any throwable object.
 * 	
 * If you want the compiler to help you check special cases that you might
 * have missed, copy all the exceptions to your own directory, change
 * "extends RuntimeException" to "extends Exception," modify your
 * CLASSPATH to look first at your own directory, later here.
 * When you compile again, the compiler will give you a huge number of
 * "Exception must be caught or declared as thrown" errors, a small
 * fraction of which will point to special cases you have overlooked.<p>
 * 
 * @author David Ellis
 * @author based on a previous version by Mark Handy
 * @version JDSL 2.1.1 
 * @see Throwable
 */
public abstract class CoreException extends RuntimeException {

    public CoreException (String message) {
	super (message);
    }
    
    public CoreException (String message, Throwable cause) {
	    super (message, cause);
    }

    public CoreException (Throwable cause) {
	    super (cause);
    }
    
}
