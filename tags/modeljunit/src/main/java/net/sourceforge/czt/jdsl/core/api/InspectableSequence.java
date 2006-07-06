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
 * Please refer to the documentation of <code>Sequence</code>. 
 *   
 * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Luca Vismara (lv)
 * @author Andrew Schwerin (schwerin)
 * @see InspectablePositionalContainer
 */

public interface InspectableSequence extends InspectablePositionalContainer {
  

  /** The first position of the sequence.
    * @return Position of the first element in the sequence
    * @exception EmptyContainerException if this sequence is empty
    */
  public Position first() throws EmptyContainerException;


  /** The last position of the sequence.
    * @return Position of the last element in the sequence
    * @exception EmptyContainerException if this sequence is empty
    */
  public Position last() throws EmptyContainerException;


  /** Check if the given position is the first.
    * @param p A Position in this sequence
    * @return True if and only if the given position is the first in the 
    * sequence
    * @exception InvalidAccessorException Thrown if <code>p</code> is 
    * not a valid position in this sequence
    */
  public boolean isFirst(Position p) throws InvalidAccessorException;

  
  /** Check if the given position is the last.
    * @param p A Position in this sequence<br>
    * @return True if and only if the given position 
    * is the last in the sequence
    * @exception InvalidAccessorException Thrown if <code>p</code> is 
    * not a valid position in this sequence
    */
  public boolean isLast(Position p) throws InvalidAccessorException;

  
  /** The previous position in the sequence.
    * @param p A Position in this sequence
    * @return Position previous to parameter position <code>p</code>
    * @exception InvalidAccessorException Thrown if <code>p</code> is 
    * not a valid position in this sequence
    * @exception BoundaryViolationException if p is the first position of 
    * this sequence.
    */
  public Position before(Position p) throws
    BoundaryViolationException, InvalidAccessorException;

  
  /** The next position in the sequence.
    * @param p A Position in this sequence.
    * @return Position after parameter position <code>p</code>
    * @exception InvalidAccessorException Thrown if <code>p</code> is 
    * not a valid position in this sequence
    * @exception BoundaryViolationException if p is the last position of 
    * this sequence.    */
  public Position after(Position p) throws
    BoundaryViolationException, InvalidAccessorException;

  
  /** Get the position in the sequence with the specified rank
    * @param rank An integer index of positions in the sequence; the
    * <code>Position</code> returned by <code>first()</code> is the
    * same as that returned by <code>atRank(0)</code), and the position
    * returned by <code>last()</code> is the same as that returned by
    * <code>atRank(size() - 1)</code>.
    * @return position at the specified rank
    * @exception BoundaryViolationException if rank<0 or rank>=size()
    **/
  public Position atRank(int rank) throws BoundaryViolationException;

  
  /** Get the rank of a given position.
    * @param p A Position in this sequence
    * @return Rank of that element, where first element has rank 0
    * and the last has rank <code>size() - 1</code>.
    * @exception InvalidAccessorException if <code>p</code> is 
    * not a valid position in this sequence
    */
  public int rankOf(Position p) throws InvalidAccessorException;
  
}
