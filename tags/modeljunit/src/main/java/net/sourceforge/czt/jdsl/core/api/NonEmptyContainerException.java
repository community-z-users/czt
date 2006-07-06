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
 * A NonEmptyContainerException indicates that the Container can't
 * fulfill the requested operation because it is not empty.
 *
 * @author David Ellis
 * @author based on a previous version by Maurizio Pizzonia
 * and Galina Shubina
 * @version JDSL 2.1.1 
 */
public class NonEmptyContainerException extends CoreException {

    public NonEmptyContainerException (String message) {
	super (message);
    }
    
    public NonEmptyContainerException (String message, Throwable cause) {
	    super(message, cause);
    }
     
    public NonEmptyContainerException (Throwable cause) {
	    super(cause);
    }

}
