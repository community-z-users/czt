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

import java.util.NoSuchElementException;
import net.sourceforge.czt.jdsl.core.api.*;



/**
 * An array-based object iterator.
 *
 * @author Ryan Shaun Baker (rsb)
 * @version JDSL 2.1.1 
 */
public class ArrayObjectIterator implements ObjectIterator {

  // protected instance variable(s)

  protected int iCurrentIndex_;
  protected int iLastIndex_;


  // private instance variable(s)

  private Object [] objectArray_;


  // protected constructor(s)

  /**
   * Uses the array to store the elements that this iterator
   * traverses.  The array is NOT copied. Takes O(N) time where N
   * is the number of elements in the array.
   *
   * @param array The elements that this iterator should traverse.
   */
  public ArrayObjectIterator (Object [] array) {
		this( array, array.length==0 ? -1 : array.length );
  }

  
  /**
   * Traverses through the array, which is not copied, until
   * num elements have been returned. Takes O(N) time where N
   * is the number of elements in the array.
   */
  public ArrayObjectIterator (Object [] array, int num) throws
  BoundaryViolationException {
    objectArray_ = array;
    iCurrentIndex_ = -1;
    iLastIndex_ = num-1;
    if (num > array.length)
      throw new BoundaryViolationException
	("The number of elements is greater than the size of the array.");
  }


    /** 
     * Takes O(1) time
     */  
  public boolean hasNext () {
    return iCurrentIndex_ < iLastIndex_;
  }

    /** 
     * Takes O(1) time
     */
  public Object nextObject() {
    if(!hasNext()) {
      throw new NoSuchElementException("End of iterator contents reached");
    }
    return objectArray_[++iCurrentIndex_];
  }

    /** 
     * Takes O(1) time
     */
    public Object object() throws NoSuchElementException {    
      
      if (iCurrentIndex_ < 0) throw new NoSuchElementException
				("iterator is in before-the-first state");
	return objectArray_[iCurrentIndex_];
    }

    /** 
     * Takes O(1) time
     */
  public void reset(){
    iCurrentIndex_ = -1;
    
  }


}
