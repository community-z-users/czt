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

import java.io.Serializable;
import net.sourceforge.czt.jdsl.core.api.*;



/**
 * An array implementation of a heap.<p>
 *
 * The number of elements that can be stored in the array or in the
 * heap is called capacity.  The capacity of the heap is always the
 * capacity of the array minus one.  The initial capacity of the array
 * is the public constant defaultInitialCapacity (or the capacity
 * specified in the constructor); the maximum capacity of the array is
 * 2^30.  The capacity of the array is doubled when needed.  The load
 * factor of the array is the ratio of the number of elements stored
 * in the array to the capacity of the array.  If array-shrinking is
 * specified at construction time, the capacity of the array is halved
 * when the load factor of the array is less than or equal to 0.25.<p>
 *
 * A binary heap such as this one has O(log n) insert, remove, and
 * replaceKey, and O(1) min.<p>
 *
 * Internal ordering is maintained according to the order of the given
 * Comparator.  Of the Comparator methods, only
 * <code>compare(.)</code> is used.
 *
 * @version JDSL 2.1.1 
 * 
 * @author Mark Handy (mdh)
 * @author Benoit Hudson (bh)
 * @author Luca Vismara (lv)
 *
 * @see Comparator
 */
public class ArrayHeap implements PriorityQueue, Serializable {

  // class variable(s)

  public static final int defaultInitialCapacity = 8;
  private static final int maxGrowableCapacity = 1 << 29;  // = 2^29
  private static final int shrinkLoadFactor = 4;

  
  // instance variable(s)

  /**
   * @serial
   */
  private AHLocator [] array_;

  /**
   * @serial
   */
  private int size_;

  /**
   * The comparator used to prioritize the keys.
   * @serial
   */
  private Comparator comp_;

  /**
   * @serial
   */
  private boolean shrink_;

  /**
   * @serial
   */
  private Locator [] locatorsArray_ = null;

  /**
   * @serial
   */
  private Object [] keysArray_ = null;

  /**
   * @serial
   */
  private Object [] elementsArray_ = null;
  
  
  // constructor(s)
  
  /**
   * Creates a new heap.  The initial capacity of the array is of
   * defaultInitialCapacity elements.  The capacity is doubled when
   * needed, and halved when the load factor of the array is less than
   * or equal to 0.25.
   *
   * @param comp the comparator to be used for comparing keys
   *
   * @exception IllegalArgumentException if comp is null
   */
  public ArrayHeap (Comparator comp) throws IllegalArgumentException {
    init(comp,defaultInitialCapacity,true);
  }

  
  /**
   * Creates a new heap.  The initial capacity of the array is of
   * defaultInitialCapacity elements.  The capacity is doubled when
   * needed, and possibly halved when the load factor of the array is
   * less than or equal to 0.25.
   *
   * @param comp the comparator to be used for comparing keys
   * @param shrink indicates whether the array should be halved when
   * the load factor of the array is less than or equal to 0.25.
   *
   * @exception IllegalArgumentException if comp is null
   */
  public ArrayHeap (Comparator comp, boolean shrink)
    throws IllegalArgumentException {
    init(comp,defaultInitialCapacity,shrink);
  }

  
  /**
   * Creates a new heap.  The capacity is doubled when needed, and
   * possibly halved when the load factor of the array is less than or
   * equal to 0.25.
   *
   * @param comp the comparator to be used for comparing keys
   * @param initialCapacity the initial capacity of the array; must be
   * a power of 2 no greater than 2^30
   * @param shrink indicates whether the array should be halved when
   * the load factor of the array is less than or equal to 0.25.
   *
   * @exception IllegalArgumentException if comp is null or
   * initialCapacity is greater than 2^30
   */
  public ArrayHeap (Comparator comp, int initialCapacity, boolean shrink)
    throws IllegalArgumentException {
    if (initialCapacity > 2*maxGrowableCapacity)
      throw new IllegalArgumentException("The initial capacity must be no"
					 +" greater than 2^30.");
    else {
      // approximate initialCapacity with the closest power of 2
      // greater than initialCapacity; this could be done more
      // efficiently with a binary search on an array storing all the
      // powers of 2 between 1 and 2^30
      int ic = 1;
      while (ic < initialCapacity)
	ic <<= 1;
      init(comp,ic,shrink);
    }
  }

  
  /**
   * A service method for the constructors.
   */
  private void init (Comparator comp, int initialCapacity, boolean shrink)
    throws IllegalArgumentException {
    if (comp == null)
      throw new IllegalArgumentException("The comparator is null.");
    else
      comp_ = comp;
    array_ = new AHLocator[initialCapacity];
    size_ = 0;
    shrink_ = shrink;
  }


  // instance method(s) from PriorityQueue

  /**
   * time complexity = worst-case O(1)
   */
  public Locator min () {
    checkEmpty();
    return array_[1];
  }


  /**
   * If array-shrinking is specified at construction time and the load
   * factor of the array is 0.25 after the removal, the capacity of
   * the array is halved by copying the elements into a new array.
   *
   * time complexity = worst-case O(log n) if array-shrinking is
   * specified at construction time, amortized O(log n) otherwise
   */
  public Object removeMin () {
    checkEmpty();

    // remove the locator
    AHLocator ahLoc = array_[1];
    ahLoc.resetContainer();

    size_--;
    if(!isEmpty()) {
      // fix the heap property: take the last element and put it
      // first, then downheap
      swap(1,size_+1);
      downheap(1);
    }
    array_[size_+1] = null;
    ensureLoadFactor();
    locatorsArray_ = null;
    keysArray_ = null;
    elementsArray_ = null;

    return ahLoc.element();
  }

  
  // instance method(s) from KeyBasedContainer

  /**
   * If the array is full, its capacity is doubled before the
   * insertion by copying the elements into a new array.
   *
   * time complexity = amortized O(log n)
   */
  public Locator insert (Object key, Object elem) {
    checkKey(key);
    ensureCapacity(size_+1);
    size_++;
    AHLocator ahLoc = new AHLocator(key,elem,size_,this);
    array_[size_] = ahLoc;
    upheap(size_);
    locatorsArray_ = null;
    keysArray_ = null;
    elementsArray_ = null;
    return ahLoc;
  }

  
  /**
   * If array-shrinking is specified at construction time and the load
   * factor of the array is 0.25 after the removal, the capacity of
   * the array is halved by copying the elements into a new array.
   *
   * time complexity = worst-case O(log n) if array-shrinking is
   * specified at construction time, amortized O(log n) otherwise
   */
  public void remove (Locator loc) {
    AHLocator ahLoc = checkContained(loc);
    int index = ahLoc.index();
    int oldsize = size_;

    // remove the old locator from the heap
    size_--;
    ahLoc.resetContainer();

    // now restore the heap properties
    if(index != oldsize) {
      // move the last-inserted key up, and put it in its right spot
      // (either upheap or downheap will do nothing)
      swap(index,oldsize);
      upheap(index);
      downheap(index);
    }
    array_[oldsize] = null;
    ensureLoadFactor();
    locatorsArray_ = null;
    keysArray_ = null;
    elementsArray_ = null;
  }

  
  /**
   * time complexity = worst-case O(log n)
   */
  public Object replaceKey (Locator loc, Object key) {
    AHLocator ahLoc = checkContained(loc);
    checkKey(key);
    int index = ahLoc.index();

    // replace the key
    Object returnKey = ahLoc.key();
    ahLoc.setKey(key);

    // restore the heap property (either upheap or downheap will do nothing)
    upheap(index);
    downheap(index);
    keysArray_ = null;

    return returnKey;
  }


  // instance method(s) from InspectableKeyBasedContainer

  /**
   * Cached for constant factor efficiency. If the container has not
   * been structurally modified and no key has been modified since the
   * last time this method was invoked, there is no need to copy the
   * elements in a new array.
   *
   * time complexity = worst-case O(n)
   */
  public ObjectIterator keys () {
    if (keysArray_ == null) {
      keysArray_ = new Object[size_];
      for (int i = 1; i <= size_; i++)
	keysArray_[i-1] = array_[i].key();
    }
    return new ArrayObjectIterator(keysArray_);
  }

  
  /**
   * Cached for constant factor efficiency. If the container has not
   * been structurally modified since the last time this method was
   * invoked, there is no need to copy the locators in a new array.
   *
   * time complexity = worst-case O(n)
   */
  public LocatorIterator locators () {
    if (locatorsArray_ == null) {
      locatorsArray_ = new Locator[size_];
      System.arraycopy(array_,1,locatorsArray_,0,size_);
    }
    return new ArrayLocatorIterator(locatorsArray_);
  }
  

  // instance method(s) from Container
  
  /**
   * time complexity = worst-case O(1)
   */
  public Container newContainer () { 
    return new ArrayHeap(comp_,shrink_); 
  }

  
  /**
   * time complexity = worst-case O(1)
   */
  public Object replaceElement (Accessor a, Object elem) {
    AHLocator ahLoc = checkContained(a);

    // replace the element
    Object returnElem = ahLoc.element();
    ahLoc.setElement(elem);
    elementsArray_ = null;

    return returnElem;
  }

  
  // instance method(s) from InspectableContainer

  /**
   * time complexity = worst-case O(1)
   */
  public boolean contains (Accessor a) {
    if (a == null)
      throw new InvalidAccessorException("The accessor is null.");
    else if (!(a instanceof AHLocator))
      return false;
    else
      return ((AHLocator)a).container() == this;
  }


  /**
   * Cached for constant factor efficiency. If the container has not
   * been structurally modified and no element has been modified since
   * the last time this method was invoked, there is no need to copy
   * the elements in a new array.
   *
   * time complexity = worst-case O(n)
   */
  public ObjectIterator elements () {
    if (elementsArray_ == null) {
      elementsArray_ = new Object[size_];
      for (int i = 1; i <= size_; i++)
	elementsArray_[i-1] = array_[i].element();
    }
    return new ArrayObjectIterator(elementsArray_);
  }

  
  /**
   * time complexity = worst-case O(1)
   */
  public boolean isEmpty () {
    return size_ == 0;
  }

  
  /**
   * time complexity = worst-case O(1)
   */
  public int size () {
    return size_;
  }


  // instance method(s) from java.lang.Object
  
  /**
   * time complexity = worst-case O(n)
   */
  public String toString () {
    return ToString.stringfor(this);
  }


  // non-interface instance method(s)

  /**
   * Creates an InspectableBinaryTree snapshot view of the heap.
   *
   * time complexity = worst-case O(n)
   *
   * @return the inspectable binary tree snapshot view
   * @exception EmptyContainerException if the prority queue is empty
   */
  public InspectableBinaryTree inspectableBinaryTree () {
    Sequence s = new NodeSequence();
    BinaryTree bt = new NodeBinaryTree();
    s.insertLast(bt.root());
    for (int i = 1; i < size_+1; i++) {
      Position p = (Position)s.removeFirst();
      bt.replaceElement(p,array_[i]);
      bt.expandExternal(p);
      s.insertLast(bt.leftChild(p));
      s.insertLast(bt.rightChild(p));
    }
//     while (!s.isEmpty()) {
//       Position p = (Position)s.removeFirst();
//       bt.replaceElement(p,Container.NULL);
//     }
    return bt;
  }

  
  /**
   * Compares the key at index i1 with that at index i2.
   */
  private int compare (int i1, int i2) {
    return comp_.compare(array_[i1].key(),array_[i2].key());
  }

  
  /**
   * Swaps the locators at index i1 with the one at index i2.
   */
  private void swap (int i1, int i2) {
    AHLocator temp = array_[i1];
    array_[i1] = array_[i2];
    array_[i1].setIndex(i1);
    array_[i2] = temp;
    array_[i2].setIndex(i2);
  }

  
  /**
   * Perform the upheap operation.  Swaps a (key,element) pair up
   * until the heap property has been restored.
   */
  private void upheap (int index) {
    array_[0] = array_[index];   // to avoid testing index > 1
    // while we are not at the root, and we are smaller than our
    // parent (at floor(index/2)), then swap us up and continue at the
    // higher level
    while (compare(index,index/2) < 0) {
      swap(index,index/2);
      index /= 2;
    }
    array_[0] = null;
  }

  
  /**
   * Performs the downheap operation.  Swaps a (key,element) pair down
   * until the heap property has been restored.
   */
  private void downheap (int index) {
    boolean even = (size_%2 == 0);
    boolean again = true;
    int candidate;

    if (even) {
      // to avoid the special case of the last leaf being a left child
      array_[size_+1] = array_[size_];
      size_++;
    }
      
    // While we are not at a leaf, and we are larger than either of our
    // children, sink down.  We may be at a leaf when going to the
    // right child would put us past the end of the array
    while (again && index <= (size_-1)/2) {
      int left = 2*index;   // left child index
      int right = 2*index+1;   // right child index
      if (compare(left,right) > 0)
	candidate = right;   // right is smaller than left
      else
	candidate = left;    // left is smaller than or equal to right
      if (compare(index,candidate) > 0) { 
	// candidate is smaller than index; it should be higher
	swap(index,candidate);   
	index = candidate;
      }
      else
	// candidate is greater than or equal to index, so we are done
	again = false;
    }

    if (even) {
      array_[size_] = null;
      size_--;
    } 
  }

  
  /** 
   * Makes sure the array is large enough; if not, double the capacity.
   */
  private void ensureCapacity (int size) {
    if (size >= array_.length) {
      if (array_.length <= maxGrowableCapacity) {
	AHLocator [] newArray = new AHLocator[array_.length*2];
	System.arraycopy(array_,1,newArray,1,array_.length-1);
	array_ = newArray;
      }
      else
	throw new FullContainerException("Maximum capacity of the priority"
					 +" queue exceeded.");
    }
  }

  
  /** 
   * Makes sure the load factor of the array is greater than
   * shrinkLoadFactor; if not, halve the capacity.
   */
  private void ensureLoadFactor () {
//     System.out.println((size_+1)+" "+array_.length+" "
// 		       +((float)(size_+1)/(float)array_.length));
//     System.out.flush();
    if (shrink_	&& size_+1 <= array_.length/shrinkLoadFactor) {
      // reduce the size
      AHLocator [] newArray = new AHLocator[array_.length/2];
      // copy the old array
      System.arraycopy(array_,1,newArray,1,size_);
      // throw away the old array and replace it with the new
      array_ = newArray;
    }
  }

  
  /**
   * Throws an exception if the container is empty.
   */
  private void checkEmpty () {
    if (isEmpty())
      throw new EmptyContainerException("ArrayHeap empty.");
  }

  
  /**
   * Throws an exception if key cannot be used by this container.
   */
  private void checkKey (Object key) {
    if (!comp_.isComparable(key))
      throw new InvalidKeyException(key+" not comparable by "+comp_+".");
  }

  
  /**
   * Throws an exception if key cannot be used by this container.
   */
  private AHLocator checkContained (Accessor a) {
    if (a == null)
      throw new InvalidAccessorException("The accessor is null.");
    else if (a instanceof AHLocator) {
      AHLocator ahLoc = (AHLocator)a;    
      if (ahLoc.container() == this)
	return ahLoc;
      else
	throw new InvalidAccessorException
	  (a+" not contained in this ArrayHeap.");
    }
    else
      throw new InvalidAccessorException("The accessor must extend"+
					 " AHLocator.");
  }


  // nested class(es)
  
  /**
   * The locator class for use within this heap.
   */
  private static class AHLocator implements Locator {

    // instance variable(s)
    
    private Object key_;
    private Object elem_;
    private int index_;
    private ArrayHeap container_;
    
    // constructor(s)

    private AHLocator (Object key, Object elem, int index,
		       ArrayHeap container) {
      key_ = key;
      elem_ = elem;
      index_ = index;
      container_ = container;
    }

    // instance method(s) from Locator

    public Object key () {
      return key_;
    }

    // instance method(s) from Accessor
    
    public Object element () {
      return elem_;
    }

    // instance method(s) from java.lang.Object
  
    public String toString () {
      return ToString.stringfor(this);
    }

    // non-interface instance methods
    
    private int index () {
      return index_;
    }
    
    private ArrayHeap container () {
      return container_;
    }

    private void setKey (Object key) {
      key_ = key;
    }
    
    private void setElement (Object elem) {
      elem_ = elem;
    }

    private void setIndex (int index) {
      index_ = index;
    }

    private void resetContainer () {
      container_ = null;
    }
    
  }   // end of class AHLocator
  
}   // end of class ArrayHeap
