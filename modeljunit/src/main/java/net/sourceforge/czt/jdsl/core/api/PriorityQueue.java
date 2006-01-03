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
 * A partially-ordered container that allows for
 * removal of the element with highest <i>priority</i>.  The names of
 * the methods (e.g., min()) assume that high priorities are
 * numerically low, but nothing except the names requires this
 * convention.
 * <p>
 * The interface makes no assumptions about how comparisons are made,
 * or how the elements are ordered.  The priority of two elements may
 * be hardcoded or chosen dynamicaly, depending upon the specific
 * implementation.
 * <p>
 * Note that there is no InspectablePriorityQueue.
 *   
 * @version JDSL 2.1.1 
 * @author Mark Handy
 * @author Andrew Schwerin
 * @author Luca Vismara
 */
public interface PriorityQueue extends KeyBasedContainer {

  
  /** 
   * Allows access to element with highest priority without removing
   * it from the priority queue.<p>
   *
   * @return the locator to the element with highest priority in the
   * priority queue
   * @exception EmptyContainerException if the priority queue is empty
   */
  public Locator min() throws EmptyContainerException;


  /** 
   * Pops the highest-priority element off the priority queue and
   * updates the priority queue.<p>
   *
   * @return an element with highest priority in the priority queue
   * @exception EmptyContainerException if the priority queue is empty
   */
  public Object removeMin() throws EmptyContainerException;

  
}
