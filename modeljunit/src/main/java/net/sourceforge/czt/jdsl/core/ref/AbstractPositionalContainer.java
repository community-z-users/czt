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

import net.sourceforge.czt.jdsl.core.api.*;



/**
 * An abstract positional container that others may extend if they do not
 * wish to deal with some of the more mundane aspects of 
 * positional containers and/or if they wish to avoid implementing themselves
 * some of the methods of container that aren't terribly pertinent to
 * a PositionalContainer.  Feel free to override any of these methods in
 * subclasses, but be certain that they work according
 * to the API in net.sourceforge.czt.jdsl.core.api.
 *
 * Also handles isEmpty() from InspectableContainer.
 *
 * @version JDSL 2.1.1 
 * @author Andrew Schwerin (schwerin)
 * @author Benoit Hudson (bh)
 * @author Ryan Shaun Baker (rsb)
 * @see PositionalContainer
 */
public abstract class AbstractPositionalContainer
  implements PositionalContainer {

  /** 
   * Works on top of PositionalContainer method
   * replaceElement(Position, Object) and InspectableContainer method
   * contains().  
   */
  public void swapElements(Position a, Position b)
    throws InvalidAccessorException {

    // Require that both of the swappees be in this container
    if((!this.contains(a)) || (!this.contains(b)))
      throw new InvalidAccessorException
	("Positions do not belong to this container");
    
    Object aelt = a.element();
    replaceElement(a,b.element());
    replaceElement(b,aelt);
    
    }

  
  /** 
   * Checks if this container is empty. 
   * Has the same time complexity as size().  If size() is O(n) and you can
   * write isEmpty() in O(1) time, then override this method.
   */
  public boolean isEmpty() { return (size() == 0); }
    
}
