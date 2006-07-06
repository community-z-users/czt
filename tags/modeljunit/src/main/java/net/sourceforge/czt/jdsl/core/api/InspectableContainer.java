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
 * A "read only" interface to a container; please see <code>Container</code>
 * for more details.
 *
 * @see Container
 * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Andrew Schwerin (schwerin)
 * @author Michael T. Goodrich
 * @author Roberto Tamassia
 * @author Luca Vismara (lv)
 */
public interface InspectableContainer {
    
  /** 
   * Gives the number of elements stored in the container.  If the
   * same element is stored in multiple places in the Container, it is
   * counted multiple times by size().  Might have time-complexity
   * O(N) for containers that are subject to split or splice
   * operations (like trees).
   *
   * @return Number of elements stored by the container.
   */
  public int size();
    
  /**
   * Checks whether this container holds zero elements.  But isEmpty()
   * is guaranteed to take constant time, while size() can be O(n).
   * @return <code>true</code> if and only if the container is empty (holds
   * no elements) 
   * @see InspectableBinaryTree
   */
  public boolean isEmpty();
  
  /**
   * Checks whether this container contains accessor <code>a</code>
   * @exception InvalidAccessorException if a is null
   */
  public boolean contains (Accessor a) throws InvalidAccessorException;

  /**
   * Returns an iterator over all the elements stored in this
   * container. No order is guaranteed, although subinterfaces or
   * implementations may make a guarantee.  The iterator returned is a
   * snapshot --
   * that is, it iterates over all objects that were elements of the container
   * at the moment that elements(.) was called, regardless of subsequent
   * modifications to the container.
   *
   * @return an iterator over all the elements stored in this
   * container
   */
  public ObjectIterator elements();
  
}
