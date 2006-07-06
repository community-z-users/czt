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
 * An implementation of Decorable using a hashtable.
 * 
 * @author Mike Boilen (mgb)
 *         <!-- initial version -->
 * @author Benoit Hudson (bh) 
 *         <!-- lazy-allocate table, smaller serialization, load factor=1 -->
 * @author Ryan Shaun Baker (rsb)
 *         <!-- port -->
 * @version JDSL 2.1.1 
 */
public class HashtableDecorable implements Decorable, java.io.Serializable {

  /**
   * A list of primes to grow to.  It's longer than you could possibly
   * need (it tops out at 1.6 billion).
   */
  private static final int[] PRIMES={ 
    5,          11,         37,        53,         97,
    193,        389,        769,       1543,       3079,
    6151,       12289,      24593,     49157,      98317,
    196613,     393241,     786433,    1572869,    3145739,
    6291469,    12582917,   25165843,  50331653,   100663319,  
    201326611,  402653189,  805306457, 1610612741
  };

  /**
   * Next cell in the list of primes.  It will grow to be the length
   * indicated by this subscript.
   */
  private transient int iNextPrime;

  /**
   * The current size of this container.  This differs from capactiy
   */
  private transient int iSize;

  /**
   * The current capacity of this container.
   */
  private transient int iCapacity;

  /**
   * The default initial capacity of this hashtable.
   */
  private static final int DEFAULT_INITIAL_CAPACITY=0;

  /**
   * Default next prime for resizing.
   */
  private static final int DEFAULT_NEXT_PRIME=0;

  /**
   * The underlying array.
   */
  private transient HashtableData[] iData;


  
  public HashtableDecorable () {
    initEmpty();
  }
    
  private final void initEmpty() {
    iData = null;
    iCapacity = 0;
    iSize = 0;
    iNextPrime = 0;
  }
    
  private final void initialAllocate() {
    iCapacity = PRIMES[iNextPrime++];
    iData = new HashtableData[iCapacity];
  }



  // public methods

  /**
   * Destroys a decoration.
   *
   * @exception InvalidAttributeException if the decoration does not exist.
   */
  public final Object destroy (Object key) throws
    InvalidAttributeException, CoreException {
    if(size()==0) {
      throw new InvalidAttributeException("Empty Decorable\n"+
					  "\tDecorable "+this+"\n"+
					  "\tkey       "+key);
    }

    // find the bucket
    int index = hash(key)%capacity();
    HashtableData current  = iData[index];
    HashtableData previous = null;
    Object ret = null;

    // search for the key in the bucket
    while(current!=null) {
      if(current.iKey==key) {
	// found; remove the node from the list
	ret=current.iElement;
	if(previous==null)
	  iData[index]=current.iNext;
	else
	  previous.iNext=current.iNext;
	iSize--;
	return ret;
      }
      previous=current;
      current=current.iNext;
    }
    throw new InvalidAttributeException("Attribute does not exist\n"+
					"\tDecorable "+this+"\n"+
					"\tkey       "+key);
  }


  /**
   * Tests if a decoration exists.
   */
  public final boolean has (Object key) {
    if(size()==0) return false;

    int index=hash(key)%capacity();
    HashtableData current=iData[index];

    while(current!=null) {
      if(current.iKey==key)return true;
      current=current.iNext;
    }
    return false;
  }


  /**
   * Sets the value of a decoration.
   */
  public final void set (Object key, Object value) throws
    InvalidAttributeException, CoreException {
    if(iSize >= iCapacity) { rehash(); }
    int index = hash(key)%capacity();

    HashtableData current = iData[index];
    while(current!=null) {
      if(current.iKey==key) {
	current.iElement=value;
	return;
      }
      current=current.iNext;
    }

    // if we're here, the key could not be found; insert at the head
    // of the list
    HashtableData toinsert = 
      new HashtableData(key, value, iData[index]);
    iData[index] = toinsert;
    iSize++;
  }


  /**
   * Gets the value of a decoration.
   */
  public final Object get (Object key) throws
    InvalidAttributeException, CoreException {
    if(size()==0) {
      throw new InvalidAttributeException("Empty Decorable\n"+
					  "\tDecorable "+this+"\n"+
					  "\tkey       "+key);
    }
    int index=hash(key)%capacity();
    HashtableData current=iData[index];
    while(current!=null) {
      if(current.iKey==key)return current.iElement;
      current=current.iNext;
    }
    throw new InvalidAttributeException("Attribute does not exist\n"+
					"\tDecorable "+this+"\n"+
					"\tkey       "+key);
  }


  public final ObjectIterator attributes () {
    Object[] toReturn = new Object[iSize];
    int index = 0;
    for (int i = 0; i < iCapacity; i++) {
      HashtableData current = iData[i];
      while (current != null) {
	toReturn[index++] = current.iKey;
	current = current.iNext;
      }
    }
    return new ArrayObjectIterator(toReturn);
  }
  
   
  /**
   * Gets the used data elements in this hashtable.
   */
  private final HashtableData[] data()
  {
    if(size()==0) return new HashtableData[0];
    HashtableData[] toRet=new HashtableData[size()];
    HashtableData current;
    int index=0;
    int curcap=capacity();
    for(int i=0;i<curcap;i++) {
      current=iData[i];
      while(current!=null) {
	toRet[index++]=current;
	current=current.iNext;
      }
    }
    return toRet;
  }

  
  /**
   * Gets the size.
   */
  protected final int size()
  {
    return iSize;
  }


  /**
   * Gets the capacity of this hashtable.  The capacity is cached to avoid
   * accessing iData.length many times.
   */
  protected final int capacity() {
    return iCapacity;
  }

  
  protected final void rehash() {
    if(iData==null) {
      initialAllocate();
    } else {
      // get the current state
      int curSize              = size();
      HashtableData curData [] = data();

      // build the new state
      iCapacity = PRIMES[iNextPrime++];
      iData     = new HashtableData[iCapacity];
      iSize     = 0;
      for(int i=0; i<curSize; i++) {
	set(curData[i].iKey,curData[i].iElement);
      }
    }
  }


  /**
   * Gets the hashcode for a particular object.  If the object is null, it
   * returns 0.  Uses System.identityHashCode (aka the address in memory).
   */
  protected final int hash(Object o)
  {
    //if(o==null)return 0;
    //what if hashcode is negative (7FFFFFFF?)
    return 0x7FFFFFFF & System.identityHashCode(o);
  }

  
  private final void writeObject(java.io.ObjectOutputStream s)
    throws java.io.IOException
  {
    // output the size of the hashtable
    s.writeInt(size());
        
    if(size()==0) return;
        
    // output all the <key,element> pairs
    HashtableData data[] = data();

    for(int i=0; i<size(); i++) {
      s.writeObject(data[i].iKey);
      s.writeObject(data[i].iElement);
      /*            Object k,e ;
		    System.out.println("dumping "+k+" => "+e);
		    System.out.println("class is "+
                    ((e==null) ? "(nil)" : e.getClass().toString()));
		    s.writeObject(k);
		    s.writeObject(e);*/
    }
  }

  
  private final void readObject(java.io.ObjectInputStream s) 
    throws java.io.IOException,ClassNotFoundException
  {
    // read the actual size
    int size=s.readInt();

    if(size==0) {
      initEmpty();
      return;
    }
    else {
      for(int iNextPrime = 0; PRIMES[iNextPrime]<size; 
	  iNextPrime++);
      iCapacity= PRIMES[iNextPrime++];

      // allocate the table, fill it.
      iData=new HashtableData[iCapacity];
      for(int i=0;i<size;i++) {
	set(s.readObject(),s.readObject());
      }
    }
  }


  // nested class(es)
  
  private static class HashtableData {
    /**
     * The key.
     */
    Object iKey;

    /**
     * The element.
     */
    Object iElement;

    /**
     * The next node in the chain.
     */
    HashtableData iNext;

    /**
     * constructs a new node with no successor.
     */
    HashtableData(Object key, Object element)
    {
      this(key,element,null);
    }

    /**
     * Constructs a new node with a successor.
     */
    HashtableData(Object key, Object element, HashtableData next)
    {
      iKey=key;
      iElement=element;
      iNext=next;
    }
  }
}
