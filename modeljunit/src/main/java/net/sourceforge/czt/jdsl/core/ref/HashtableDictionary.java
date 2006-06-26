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
import java.util.Vector;

/** 
 * An implementation of Dictionary using a chaining hashtable.
 * Elements are inserted at the front of each chain, to ensure a
 * constant time bound (disregarding resizing overhead).
 * <p>
 * The chains have references to both the next and previous element in
 * the chains to make remove(Locator) guaranteed constant time
 * (again, disregarding resizing overhead).
 * <p>
 * In the time complexities listed for the methods, O(1) is constant
 * time, O(N) is time proportional to the number of elements in the
 * data structure, and O(C) is time proportional to the capacity of
 * the data structure.
 * 
 * @author Mike Boilen (mgb)
 *         <!initial version>
 * @author Benoit Hudson (bh) 
 *         <!lazy-allocate table, smaller serialization, load factor=1>
 * @author Ryan Shaun Baker (rsb)
 *         <!port>
 * @author Keith Schmidt (kas)
 *         <!-- dictionary interface -->
 * @version JDSL 2.1.1 
 */

public class HashtableDictionary extends AbstractDictionary 
  implements Dictionary, java.io.Serializable {

    /**
     * A list of primes to grow to.  It's longer than you could possibly
     * need (it tops out at 1.6 billion).
     */
    private static final int[] PRIMES={  
      3,           5,          11,         37,        53,
      97,          193,        389,        769,       1543,
      3079,        6151,       12289,      24593,     49157,
      98317,       196613,     393241,     786433,    1572869,
      3145739,     6291469,    12582917,   25165843,  50331653,
      100663319/*,   201326611,  402653189,  805306457, 1610612741*/

      // according to the Java VM spec no array larger than 134217727
      // can exist, so the primes larger than this will not be
      // available until the spec changes.
    };


    /**  
     * Next index into the array of primes. Rehashing will cause the
     * capacity to grow to be the number in PRIMES indicated by this
     * subscript.  e.g. capacity <-- PRIMES[nextPrime_]
     */
    private transient int nextPrime_;

    /**
     * The current number of data elements stored in this container.
     */
    private transient int size_;

    /** 
     * The current capacity of this container. i.e. how much it can
     * hold before being resized.  
     */
    private transient int capacity_;

    /**
     * The default initial capacity of this hashtable.
     */
    private static final int DEFAULT_INITIAL_CAPACITY=0;

    /**
     * The underlying array.
     */
    private transient HashtableData[] data_;

    /**
     * @serial
     */
    private Locator[] locatorCache_ = null;

    /**
     * @serial
     */
    private Object[] keyCache_ = null;

    /**
     * @serial
     */
    private Object[] elementCache_ = null;

    /** 
     *The comparator which is used to test for comparability and
     * equality of keys.  
     * @serial
     */
    private HashComparator comp_;

    /**
      * This constructor takes a Comparator which can determine if it
      * can compare a key, and if two keys are equal, nothing more.  
      */
    public HashtableDictionary (HashComparator comp) {
      this(comp, DEFAULT_INITIAL_CAPACITY);
    }
    
    /**
      * This constructor takes a Comparator
      * which can determine if it can compare a key, and if two keys
      * are equal, nothing more, and an integer denoting the initial capacity.
      */
    public HashtableDictionary (HashComparator comp, int initCap) {
      if (initCap > PRIMES[PRIMES.length-1]) {
	throw new IllegalArgumentException("specified initial capacity: "+
					   initCap+" is greater than largest"+
					   " allowable capacity: "+
					   PRIMES[PRIMES.length-1]);
      }
      comp_ = comp;
      size_ = 0;
      for (nextPrime_ = 0;PRIMES[nextPrime_] < initCap;nextPrime_++);
      capacity_ = PRIMES[nextPrime_++];
      data_ = new HashtableData[capacity_];  
    }
    
    /**
      * A convenience method to avoid repeating code in the
      * deserialization code.
      */
    private void initEmpty() {
      size_ = 0;
      nextPrime_ = 0;
      capacity_ = PRIMES[nextPrime_++];
      data_ = new HashtableData[capacity_];
    }

    // public methods

    /**
      * O(1)
      */
    public final int size() {return size_;}

    /**
      * O(1)
      */
    public boolean isEmpty() {return (size_ == 0);}
  
    /**
      * O(1)
      */
    public Object replaceElement(Accessor acc, Object Element) {
      HashtableData toSetElt = checkContained(acc);
      Object toReturn = toSetElt.element();
      toSetElt.setElement(Element);
      // clear element cache
      clearElementCache();
      return toReturn;
    }

    /**
      * O(1)
      */
    public Container newContainer() {
      return new HashtableDictionary(comp_);
    }

    /**
      * O(1)
      */
    public boolean contains(Accessor acc) {
      if (acc == null)
	throw new InvalidAccessorException("Accessor is null.");
      else if (acc instanceof HashtableData)
	return (((HashtableData)acc).container() == this);
      else 
	return false;
    }

    /**
      * O(1) expected, O(N) if insertion pushes the size above the
      * rehashing threshhold.
      */
    void insert(Locator loc) 
      throws InvalidAccessorException {
	HashtableData toInsert = castData(loc);
	if (toInsert.container() != null)
	  throw new InvalidAccessorException("Locator is already contained.");
	rehash(); // rehash performs size >= capacity check.
	int index = dataIndex(toInsert.key());

	// you're one of mine now, y'hear?
	toInsert.setContainer(this);

	// We want to allow multiple elements with the same
	// key. always insert a new one.
	toInsert.setNext(data_[index]);
	if (data_[index] != null)
	  data_[index].setPrev(toInsert); 
	toInsert.setPrev(null); // chain is null terminated at both ends
	data_[index] = toInsert;
	size_++;
	// structure has changed. clearall caches
	clearCaches();
    }

    /**
      * O(1) expected: strictly O(1) unless removal reduces size
      * below the downhashing threshhold, in which case it is O(N)
      */
    public void remove(Locator loc)
      throws InvalidAccessorException {
	HashtableData toRemove = checkContained(loc);
    
	// fix up the pointers in the chains.
	if (toRemove.prev() != null)
	  (toRemove.prev()).setNext(toRemove.next());
	else { // we are at the front of the chain
	  int index = dataIndex(toRemove.key());
	  data_[index]=toRemove.next();
	}
	if (toRemove.next() != null)
	  (toRemove.next()).setPrev(toRemove.prev());
	// make the locator uncontained.
	toRemove.setContainer(null);
	size_--;
	// trim the size if it is excessive.
	downhash(); // downhash performs the size << capacity check.
	// structure has changed. clear all caches
	clearCaches();
    }
  
    /**
      * O(1)
      */
    public Object replaceKey(Locator loc, Object key){
      HashtableData toUpdate = checkContained(loc);
      checkKey(key);
      remove(toUpdate);
      Object toReturn = toUpdate.key();
      toUpdate.setKey(key);
      insert(toUpdate);
      // structure has changed. clear all caches
      clearCaches();
      return toReturn;
    }

    /**
      * O(1) if structure hasn't changed, O(N) otherwise.
      */
    public LocatorIterator locators() {
      if (locatorCache_ == null) {
	locatorCache_ = data();
      }
      return new ArrayLocatorIterator(locatorCache_);
    }

    // Regarding snapshotKeys and snapshotElements
    //
    // We assume that it is faster to step through an array than to
    // traverse all the chains in every slot of the hashtable.
    //
    // If we have a valid locatorCache_, it is faster to build the
    // array of keys/elements from it instead of traversing the
    // structure again, as the capacity may be significanly larger
    // than the size. If we don't, the constant factor increase caused
    // by generating the locator array is <= 2 and may be offset in
    // calls to the other snapshot methods

    /**
      * O(1) if structure hasn't changed, O(N) otherwise.
      */
    public ObjectIterator keys() {
      if (keyCache_ == null) {
	if (locatorCache_ == null) {
	  locatorCache_ = data();
	}
	keyCache_ = new Object[locatorCache_.length];
	for (int i =0; i < locatorCache_.length; i++)
	  keyCache_[i] = locatorCache_[i].key();
      }
      Object[] toBuild = new Object[0];
      if (keyCache_ != null) // Iterator can't be constructed with null
	toBuild = keyCache_;
      return new ArrayObjectIterator(toBuild);
    }

    /**
      * O(1) if structure *AND* elements haven't changed, O(N)
      * otherwise.
      */
    public ObjectIterator elements() {
      if (elementCache_ == null) {
	if (locatorCache_ == null) {
	  locatorCache_ = data();
	}
	elementCache_ = new Object[locatorCache_.length];
	for (int i =0; i < locatorCache_.length; i++) {
	  elementCache_[i] = locatorCache_[i].element();
	}
      }
      Object[] toBuild = new Object[0];
      if (elementCache_ != null) // Iterator can't be constructed with null
	toBuild = elementCache_;
       return new ArrayObjectIterator(toBuild);
    }

    /**
      * O(#elts with target key), worst case O(N)
      */
    public LocatorIterator findAll(Object key)
      throws InvalidKeyException {
      checkKey(key);
      int index=dataIndex(key);
      HashtableData current=data_[index];
      Vector storeAll = new Vector();
      while(current!=null) {
	if(comp_.isEqualTo(current.key(),key)) {
	  storeAll.addElement(current);
	}
	current=current.next();
      }
      // set up the LocatorIterator, which takes a Locator[] as a param.
      Locator[] toReturn = new Locator[storeAll.size()];
      storeAll.copyInto( toReturn );
      return new ArrayLocatorIterator(toReturn);
    }

    /** 
      * O(#elts with target key) expected, worst case O(N) with
      * excessive chaining, or if removeAll drops the size below the
      * downhashing threshhold.
      */
    public LocatorIterator removeAll(Object key) {
      checkKey(key);
      int index=dataIndex(key);
      HashtableData current=data_[index];
      HashtableData next = null;
      Vector storeAll = new Vector();
      while(current!=null) {
	next = current.next();
	if(comp_.isEqualTo(current.key(),key)) {
	  remove(current); //remove performs downhashing as needed.
	  storeAll.addElement(current);
	}
	current=next;
      }
      // structure has changed. clear all caches
      clearCaches();
      // set up the LocatorIterator, which takes a Locator[] as a param.
      Locator[] toReturn = new Locator[storeAll.size()];
      storeAll.copyInto( toReturn );
      return new ArrayLocatorIterator(toReturn);
    }

    /**
      * Removes the first element found with the given key from the
      * hashtable.
      * O(1) -- expected. will be O(N) with excessive chaining
      * or if removal reduces below the downhashing threshhold.
      *
      * @exception InvalidKeyException if the key cannot be compared 
      */    
    public Locator removeKey(Object key) 
      throws InvalidKeyException {
	  /* mdh: commented out Keith's code in an effort to remove
	     a bug that Lixin found, that gives a bad-index exception in
	     the	  toRet[index++]=current;     line of data().
	     I think the bug is that the chain-repairing code below doesn't
	     reset the array-slot's pointer in the special case when the
	     node being removed is at the front of the list, thus leaving
	     a "removed" node in the list to be seen later.
	     */
	  Locator toret = find( key );
	  if( toret != NO_SUCH_KEY ) remove( toret );
	  return toret;
	  /*
	  // find(key) checks for invalid keys.
	  HashtableData toRemove = (HashtableData)(find(key));
	  
	  if (toRemove != NO_SUCH_KEY) {
	      // link the chain around the removed node.
	      if (toRemove.prev() != null)
		  (toRemove.prev()).setNext(toRemove.next());
	      if (toRemove.next() != null)
		  (toRemove.next()).setPrev(toRemove.prev());
	      // make the locator uncontained.
	      toRemove.setContainer(null);
	      size_--;
	      // trim the size if it is excessive.
	      downhash(); // downhash performs the size << capacity check.
	      // structure has changed. clear all caches
	      clearCaches();
	  }
	  return toRemove;
	  */
    }


    /**
      * O(1) expected, O(N) if insertion pushes the size above the
      * rehashing threshhold.
      */
    public Locator insert(Object key, Object value) 
      throws InvalidKeyException {
	checkKey(key);
	rehash(); // rehash performs size >= capacity check.
	int index = dataIndex(key);
      
	// We want to allow multiple elements with the same
	// key. always insert a new one.
	HashtableData toInsert = 
	  new HashtableData(key, value, this, data_[index], null);
 
	data_[index] = toInsert;
	size_++;
	// structure has changed. clear all caches
	clearCaches();
	return toInsert;
    }

    /**
      * O(1) -- expected, O(N) worst case with excessive chaining.
      */
    public Locator find (Object key) 
      throws InvalidKeyException {
      checkKey(key);
      int index=dataIndex(key);
      HashtableData current=data_[index];
      while(current!=null) {
	if(comp_.isEqualTo(current.key(),key))
	  return current;
	current=current.next();
      }
      return NO_SUCH_KEY;
    }
     
    /**
      * O(N+C) Returns an array of all the Locators in this hashtable.
      */
    private HashtableData[] data() {
      if(size()==0) return new HashtableData[0];
      HashtableData[] toRet=new HashtableData[size()];
      HashtableData current;
      int index=0;
      int curcap=capacity();
      for(int i=0;i<curcap;i++) {
	current=data_[i];
	while(current!=null) {
	  toRet[index++]=current;
	  current=current.next();
	}
      }
      return toRet;
    }

    /** 
      * O(1) Gets the capacity of this hashtable.  The capacity is
      * cached to avoid accessing data_.length many times.  
      */
    private int capacity() {
      return capacity_;
    }

    /**
     * O(N) this method increases the capacity of the hashtable when
     * the current capacity is reached and rehashes all of the
     * elements into the larger hashtable.  
     */
    private void rehash() {
      if(size_==0) {
	initEmpty();
      } 
      else if (nextPrime_ >= PRIMES.length) {
	throw new FullContainerException("Hashtable cannot hold any more data elements");
      }
      else if (size() >= capacity()){
	rebuildTable();
      }
    }

    /**
     * O(N+C) This method reduces the capacity of the hashtable when
     * the size becomes sufficiently small.  
     */
    private void downhash() {
      if(size_==0) {
	initEmpty();
      }
      else {
	// get the 1st prime larger than the size of the container
	int currPrime;
	for (currPrime = 0;PRIMES[currPrime] < size();currPrime++);
	// if currPrime = nextPrime_-1, the same table will be
	// created.  if currPrime = nextPrime_, a larger table will be
	// created.  if currPrime > nextPrime_, duck and cover, thes
	// baby's about to blow.
	if (currPrime < nextPrime_ -1) {
	  nextPrime_ = currPrime +1;// ensure capacity != size + (a
	                            // small constant)
	  rebuildTable();
	}
      }
    }
    
    /** 
     * O(N+C) This method rebuilds the hashtable with capacity
     * PRIMES[nextPrime_], and increments nextPrime_ in anticipation
     * of the next increase in capacity. 
     */
    private void rebuildTable() {
      // get the current state
      int currSize             = size();
      HashtableData currData[] = data();
      HashtableData toInsert; // temporary storage in the for loop
      int index; // the table slot at which to insert the datum.

      // build the new state
      capacity_ = PRIMES[nextPrime_++];
      data_     = new HashtableData[capacity_];
      size_     = 0;
      for(int i=0; i<currSize; i++) {
	// simple insertion code 
	toInsert = currData[i];
	index = dataIndex(toInsert.key());
	toInsert.setNext(data_[index]);
	if (data_[index] != null)
	  data_[index].setPrev(toInsert); 
	toInsert.setPrev(null); // chain is null terminated at both ends
	data_[index] = toInsert;
	size_++;
      }
      // structure has changed. clear all caches
      clearCaches();
    }

    /**
      * Writes a HashtableDictionary out to a serialized form.
      *
      *@exception java.io.IOException
      */
    private void writeObject(java.io.ObjectOutputStream s)
      throws java.io.IOException {
      // output the size of the hashtable
      s.writeInt(size());
        
      if(size()==0) return;
        
      // output all the <key,element> pairs
      HashtableData data[] = data();

      for(int i=0; i<size(); i++) {
	s.writeObject(data[i].key());
	s.writeObject(data[i].element());
      }
    }

    /**
      * Reads a HashtableDictionary in from a serialized form.
      *
      *@exception java.io.IOException
      *@exception java.lang.ClassNotFoundException
      */
    private void readObject(java.io.ObjectInputStream s) 
      throws java.io.IOException,ClassNotFoundException {
      // read the actual size
      int size=s.readInt();

      if(size==0) {
	initEmpty();
	return;
      }
      else {
	for(int nextPrime_ = 0; PRIMES[nextPrime_]<size; 
	    nextPrime_++);
	capacity_= PRIMES[nextPrime_];

	// allocate the table, fill it.
	data_=new HashtableData[capacity_];
	for(int i=0;i<size;i++) {
	  insert(s.readObject(),s.readObject());
	}
      }
    }

    /** 
      * Convenience method to test if a given accessor is contained
      * within this data structure.
      *
      *@exception InvalidAccessorException
      */
    private HashtableData checkContained(Accessor acc)
      throws InvalidAccessorException {
	HashtableData toCast = castData(acc);
	if (toCast.container() != this)
	  throw new InvalidAccessorException("Accessor is contained in another data structure.");
	return toCast;
    }

    /** 
      * Convenience method to test if a given accessor is of the
      * appropriate type for this here hashtable.
      *
      *@exception InvalidAccessorException
      */
    private HashtableData castData(Accessor acc)
      throws InvalidAccessorException {
	if (acc==null)
	  throw new InvalidAccessorException("Accessor is null.");
	else if (acc instanceof HashtableData) {
	  return (HashtableData)acc; 
	}
	else 
	  throw new InvalidAccessorException("Accessor must extend HashtableData.");
    }

    /** 
      * Convenience method to test if a given key is of the
      * appropriate type for this here hashtable.
      *
      *@exception InvalidKeyException
      */
    private void checkKey(Object key) {
      if (!(comp_.isComparable(key)))
	throw new InvalidKeyException("Key is of inappropriate type.");   
    }
  
    /** 
      * O(N) human readable description of the contents of this
      * dictionary, conforming to the Collections spec for key-element
      * structures.  
      */
    public String toString() {
      return ToString.stringfor(this);
    }

    /**
      * O(1) this method clears all of the caches used in Iterator
      * generation and should be called after every structural change
      * to the Container.  
      */
    private void clearCaches() {
      locatorCache_ = null;
      keyCache_ = null;
      elementCache_ = null;
    }

    /** 
      * O(1) this method clears the element cache. it should be called
      * after replaceElement(.)  
      */
    private void clearElementCache() {
      elementCache_ = null;
    }

    /**
      * O(1) computes the hash value of the object with the
      * HashComparator and reduces it modulo the size of the
      * underlying array.  
      */
    private int dataIndex(Object key) {
      return (comp_.hashValue(key)%capacity());
    }


  // nested class(es)
  
  /** 
   * This is the implementation of the Locator interface used
   * within the hashtable.  
   */
  private static class HashtableData implements Locator{
    /**
     * The key.  
     */
    private Object iKey;
    /**
     * The element.
     */
    private Object iElement;
    /**
     * The next node in the chain.
     */
    private HashtableData iNext;
    /**
     * The previous node in the chain.
     */
    private HashtableData iPrev;
    /** 
     *The net.sourceforge.czt.jdsl.core.api.Container in which this Locator resides 
     */
    private Container iContainer;
    /**
     * constructs a new node with no successor or predecessor.
     */
    HashtableData(Object key, Object element, Container cont) {
      this(key,element,cont,null, null);
    }
    /**
     * Constructs a new node with a successor and a predecessor.
     */
    HashtableData(Object key, Object element, Container cont, 
		  HashtableData next, HashtableData prev) {
      iKey=key;
      iElement=element;
      iContainer=cont;
      iNext=next;
      if (iNext != null)
	iNext.setPrev(this);
      iPrev=prev;
      if (iPrev != null)
	iPrev.setNext(this);
    }
    
    /**
     * O(1) accessor for the key held by this Locator
     */
    public Object key() {return iKey;}
    
    /**
     * O(1) accessor for the element held by this Locator
     */
    public Object element() {return iElement;}
    
    /**
     * O(1) accessor for the Container which holds Locator
     */
    private Container container() {return iContainer;}
    
    /**
     * O(1) accessor for the next Locator in the chain
     */
    private HashtableData next() {return iNext;}
    
    /**
     * O(1) accessor for the previous Locator in the chain
     */
    private HashtableData prev() {return iPrev;}
    
    
    /**
     * O(1) mutator for the key held by this Locator
     */
    private void setKey(Object newKey) {iKey = newKey;}
    
    /**
     * O(1) mutator for the element held by this Locator
     */
    private void setElement(Object newElement) {iElement = newElement;}
    
    /**
     * O(1) mutator for the next Locator in the chain
     */
    private void setNext(HashtableData newNext) {iNext = newNext;}
    
    /**
     * O(1) mutator for the previous Locator in the chain
     */
    private void setPrev(HashtableData newPrev) {iPrev = newPrev;}
    
    /**
     * O(1) mutator for the Container which holds Locator
     */
    private void setContainer(Container newCont) {iContainer = newCont;}
    
    
    /** 
     * O(1) human readable description of the contents of this
     * locator, conforming to the Collections spec for key-element
     * structures.  
     */
    public String toString () {
      return ToString.stringfor(this);
    }
  }
}
