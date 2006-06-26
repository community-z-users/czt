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
 * A class abstracting the common parts of ArrayPositionIterator and
 * ArrayLocatorIterator.
 *
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public abstract class AbstractArrayIterator {

  // protected instance variable(s)

  protected int iCurrentIndex_;
  protected int iLastIndex_;


  // private instance variable(s)

  private Accessor [] accessorArray_;


  // protected constructor(s)

  /**
   * Uses the array to store the elements that this iterator
   * traverses.  The array is NOT copied.
   *
   * @param array The elements that this iterator should traverse.
   */
  protected AbstractArrayIterator (Accessor [] array) {
    accessorArray_ = array;
    iCurrentIndex_ = -1;
    if (array != null) {
      iLastIndex_ = array.length-1;
    }
    else {
      iLastIndex_ = -1;
    }
  }

  
  /**
   * Traverses through the array until the first
   * num elements have been returned. The array is NOT copied.
   */
  protected AbstractArrayIterator (Accessor [] array, int num) throws
  BoundaryViolationException {
    accessorArray_ = array;
    iCurrentIndex_ = -1;
    iLastIndex_ = num-1;
    if (num > array.length)
      throw new BoundaryViolationException
	("The number of elements is greater than the size of the array.");
  }


  // public instance method(s) 
  
  public boolean hasNext () {
    return iCurrentIndex_ < iLastIndex_;
  }

  
  public Object element () throws NoSuchElementException {
    checkBeforeStart();
    return accessorArray_[iCurrentIndex_].element();
  }

  /** 
   * Takes O(1) time
   */
  public Object nextObject() {
    return nextAccessor();
  }

  /** 
   * Takes O(1) time
   */
  public Object object() throws NoSuchElementException {    
    checkBeforeStart();
    return accessorArray_[iCurrentIndex_];
  }

  /** 
   * Takes O(1) time
   */
  public void reset(){
    iCurrentIndex_ = -1;
  }


  // protected instance method(s)

  protected void checkBeforeStart () throws NoSuchElementException {
    if (iCurrentIndex_ < 0) throw new NoSuchElementException
				("iterator is in before-the-first state");
  }


  protected Accessor nextAccessor() {
    if(!hasNext()) {
      throw new NoSuchElementException("End of iterator contents reached");
    }
    return accessorArray_[++iCurrentIndex_];
  }

}
