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
 * An array-based locator iterator.
 *
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public class ArrayLocatorIterator extends AbstractArrayIterator
implements LocatorIterator {

    // protected instance variable(s)
    protected Locator [] locArray_;
    
    
    // public constructor(s)
    
    /**
     * Uses the array to store the elements that this iterator
     * traverses.  The array is NOT copied.
     *
     * @param array The elements that this iterator should traverse.
     */
    public ArrayLocatorIterator (Locator [] array) {
	super(array);
	locArray_ = array;
    }
    
    
    /**
     * Traverses through the array, which is not copied, until
     * num elements have been returned.
     */
    public ArrayLocatorIterator (Locator [] array, int num) throws
    BoundaryViolationException {
	super(array,num);
	locArray_ = array;
    }
    
    
    // public instance method(s) from KeyBasedIterator
    
    public Locator locator() throws NoSuchElementException {    
	checkBeforeStart();
	return locArray_[iCurrentIndex_];
    }
    
    public Object key() throws NoSuchElementException {
	checkBeforeStart();
	return locArray_[iCurrentIndex_].key();
    }
    
    public Locator nextLocator() throws NoSuchElementException {
	return (Locator) super.nextAccessor();
    }
    
}
