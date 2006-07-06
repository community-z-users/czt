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
  * A positional container whose elements
  * are linearly organized. It is a generalization of stacks, queues,
  * linked lists, and arrays.</P>
  *   
  * <P>For a Sequence, methods <code>InspectableContainer.elements()</code>
  * and <code>InspectablePositionalContainer.positions()
  * are guaranteed to return iterators in first-to-last order.</P>
  *   
  * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Luca Vismara (lv)
 * @author Andrew Schwerin (schwerin)
  * @see InspectableSequence
  * @see PositionalContainer
  */
public interface Sequence extends InspectableSequence, PositionalContainer {
  
  // Five insertion methods that take an Object element, and return
  // the position of the element after inserting it into the sequence.
  
  /** 
    * Inserts an object as <i>first</i> element of the sequence
    * @param element Any java.lang.Object
    * @return The <code>Position</code> containing that <code>element</code>, 
    * which is now the first position in the sequence.
    */
  public Position insertFirst (Object element);

  
  /** 
    * Inserts an object as <i>last</i> element of the sequence.
    * @param element Any java.lang.Object
    * @return The <code>Position</code> containing that <code>element</code>, 
    * which is now the last in the sequence.
    */
  public Position insertLast (Object element);

  
  /**  Inserts an object <i>before</i> a position in the sequence.
    * @param p Position in this sequence before which to insert an 
    * element.
    * @param element Any java.lang.Object<br>
    * @return Position containing <code>element</code> and before
    * <code>Position p</code>.
    * @exception InvalidAccessorException Thrown if <code>p</code> is 
    * not a valid position in this sequence
    */
  public Position insertBefore (Position p, Object element) throws
    InvalidAccessorException;

  
  /** 
    * Inserts an object <i>after</i> a position in the sequence.  
    * @param p Position in this sequence after which to insert an
    * element.
    * @param element Any java.lang.Object<br>
    * @return Position containing <code>element</code> and after
    * <code>Position p</code>.
    * @exception InvalidAccessorException Thrown if <code>p</code> is 
    * not a valid position in this sequence
    */
  public Position insertAfter (Position p, Object element) throws
    InvalidAccessorException;

  
  /** 
    * Inserts based on an integer rank similar to array indices.
    * The first element in the sequence has rank 0, and the last has rank
    * <code>size() - 1</code>.  It is valid to insert at any rank greater
    * than or equal to zero and less than or equal to <code>size()</code>.
    *
    * @param rank Rank that <code>element</code> should have after insertion.
    * @param element Any java.lang.Object<br>
    * @return Position of <code>element</code> in the sequence.
    * @exception BoundaryViolationException if <code>rank</code> exceeds
    * <code>size()</code> or if 0 exceeds <code>rank</code>
    */
  public Position insertAtRank (int rank, Object element) throws
    BoundaryViolationException;
  

  //remove methods
  
  /** 
    * Removes and invalidates the first position of this.
    * 
    * @return the element formerly stored at the first position of this
    * @exception EmptyContainerException if this sequence is empty
    */
  public Object removeFirst () throws EmptyContainerException;

  
  /** 
    * Removes and invalidates the last position of this.
    *
    * @return the element formerly stored at the last position of this
    * @exception EmptyContainerException if this sequence is empty
    */
  public Object removeLast () throws EmptyContainerException;


  /**  Removes and invalidates the specified position
    *
    * @param pos the position to be removed
    * @return the element formerly stored at pos
    * @exception InvalidAccessorException if the specified position is 
    * invalid or not belong to this container.
    */
  public Object remove (Position pos) throws InvalidAccessorException;

  
  /** Remove and invalidates the position after the position
    * specified
    *
    * @param pos a position
    * @return the element formerly stored at the position after pos
    * @exception BoundaryViolationException if pos is the last position of this
    * sequence 
    * @exception InvalidAccessorException if the specified position is 
    * invalid or not belong to this container. 
    */

  public Object removeAfter (Position pos) 
    throws BoundaryViolationException, InvalidAccessorException;

  
  /** 
    * Removes and invalidates the position before the position specified.
    *
    * @param pos a position
    * @return the element formerly stored at the position before pos
    * @exception BoundaryViolationException if pos is the first position of 
    * this sequence.
    * @exception InvalidAccessorException if the specified position is 
    * invalid or not belong to this container. 
    */

  public Object removeBefore (Position pos) throws BoundaryViolationException,
    InvalidAccessorException;


  /** 
    * Removes and invalidates the position at the specified rank
    *
    * @param rank the rank of the position to be removed
    * @return the element formerly stored at the position at rank
    * @exception BoundaryViolationException if rank is less than 0 or greater
    * than the size of this sequence
    */
  public Object removeAtRank (int rank) throws BoundaryViolationException;

}
