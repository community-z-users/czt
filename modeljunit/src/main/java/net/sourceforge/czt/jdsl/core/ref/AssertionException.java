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

package net.sourceforge.czt.jdsl.core.ref;

import net.sourceforge.czt.jdsl.core.api.CoreException;



/**
 * This exception indicates that an internal check has failed.  A correctly
 * functioning program will never cause this to be thrown.
 *
 * @author David Ellis
 * @author based on a previous version by Mark Handy
 * @version JDSL 2.1.1 
 * @deprecated Starting with Java 2 version 1.4 assertions are part of
 * the language, and thus this class is no longer necessary.
 */
public class AssertionException extends CoreException {

  public AssertionException () {
    super("assertion failed");
  }
  
  public AssertionException (String message) {
    super(message);
  }
  public AssertionException (String message, Throwable cause) {
	  super(message, cause);
  }
   
  public AssertionException (Throwable cause) {
	  super(cause);
  }
}
