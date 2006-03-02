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
  * A Sequence implemented on top of an array. <p>
  *
  * In this design, the Sequence's Positions keep track of their ranks 
  * in the Sequence, making all atRank(int) operations O(1) time. 
  * The Positions also keep track of their Container (the Sequence), 
  * so the Sequence's contains(Accessor) method takes O(1) time.
  
  * <p>
  * The array is used in a circular fashion -- the first Position in
  * the Sequence can occupy any index in the array, and the Sequence's
  * subsequent Positions may wrap around the end of the array to occupy
  * indices at the front of the array. 
  * Insertion and removal operations generally take O(n) time.
  * When items are inserted into or removed from the Sequence, Positions
  * must be shifted up or down the array to make room for the new Position.
  * In these cases, the design of the shifting operation ensures that 
  * the minimum number of Positions are moved around. In any insertion
  * or removal operation, no more than n/2 Positions will be shifted
  * in the array (where n is the total number of items in the Sequence). 
  * The methods insertFirst(Obj), insertLast(Obj), posInsertFirst(Pos), 
  * posInsertLast(Pos), removeFirst(), and removeLast() generally take
  * O(1) time, since no internal shifting is required. But when the
  * array has to be reallocated and copied, these methods take O(n) time.
  
  * <p>
  * The capacity of the Sequence is equal to the capacity of the 
  * underlying array. Whenever the size of the Sequence becomes equal to 
  * the size of the underlying array, the next insertion operation will
  * cause the array to double in size. The load factor of the array is the
  * ratio of the number of elements stored in the array to the capacity of 
  * the array. The capacity of the array is possibly halved when the load
  * factor of the array falls below 0.25. 
  * The initial capacity of the array is 16 (or the capacity in the constructor).
  * The maximum capacity of the array is 2^26. If a client attempts to
  * exceed this maximum, a ContainerFullException is thrown.
  
  * <p>
  * This ArraySequence incorporates the iterator caching optimization:
  * calls to iterator-returning methods are amortized
  * O(n/k) time if called k times between 
  * modifications of the sequence. This is accomplished by making a list of
  * the Positions of the sequence whenever iterating through
  * the list is necessary, and using it until there is a modification
  * to the Sequence. <p>
  *
 * @author Lucy Perry (lep)
 * @author Mark Handy (mdh)
 * @author Jitchaya Buranahirun (jbr)
 * @author Benoit Hudson (bh)
 * @author Ryan Shaun Baker (rsb)
  *
  * @version JDSL 2.1.1 
  */
public class ArraySequence extends AbstractPositionalContainer
implements Sequence {
  


  /**
    * The stored size of the Sequence -- modified on insertion or removal.
    */
  private int size_;


  /**
    * The size of the underlying array
    */
  private int array_size_;


  /**
    * Index of the first Position of the Sequence
    */
  private int first_;


  /**
    * Underlying array for Positions
    */
  private ArrayPos positions_[];

  /**
    * Cache for Positions; Discarded upon modification.
    */
  private Position cPos_[];

  /**
    * Cache for elements; Discarded upon modification.
    */
  private Object cElts_[];

  /**
    * Initial capacity for the Sequence & underlying array.
    * The array will never shrink below this capacity.
    */
  private int init_cap_;


  /**
    * Whether the array should be halved when the load factor of the 
    * array is less than or equal to 0.25.
    */
  private boolean permit_shrinkage_;


  /**
    * This is used to ensure that the array never shrinks until 
    * it has overflowed at least once.
    */
  private boolean array_has_grown_;



  // **** some constants ****
  private static final int MAX_CAPACITY = 1 << 26;// == 2^26
  private static final int SHRINK_LOAD_FACTOR = 4;

  // **** some default vals -- client can override w/ special constructors ****
  private static final int DEFAULT_INIT_CAP = 16;
  private static final boolean DEFAULT_PERMIT_SHRINKAGE = true;



  /**
    * The default constructor for ArraySequence
    * Initial array capacity defaults to 16.
    * The array is shrinkable by default.
    */
  public ArraySequence(){
    super();
    init(DEFAULT_INIT_CAP, DEFAULT_PERMIT_SHRINKAGE);
  }


  /**
    * Creates an empty Sequence. 
    * Uses the given initial capacity for the array.
    */
  public ArraySequence(int initialCapacity){
    super();
    int realCap = initCapacity(initialCapacity);
    init(realCap, DEFAULT_PERMIT_SHRINKAGE);
  }


  /**
    * Creates an empty Sequence.
    * Lets the client specify non-shrinkable.
    * Uses default inital array capacity of 16.
    */
  public ArraySequence(boolean permitShrinkage){
    super();
    init(DEFAULT_INIT_CAP, permitShrinkage);
  }


  /**
    * Creates an empty Sequence.
    * Lets the client specify the array's initial capacity,
    * and whether the array is shrinkable.
    */
  public ArraySequence(int initialCapacity, boolean permitShrinkage){
    int realCap = initCapacity(initialCapacity);
    init(realCap, permitShrinkage);
  }
    

  /*
    A service method used by the constructors.
  */
  private final void init(int initialCapacity, boolean permitShrinkage){
    size_ = 0;
    first_ = -1;

    positions_ = new ArrayPos[initialCapacity];  
    array_size_ = initialCapacity;
    init_cap_ = initialCapacity;
    permit_shrinkage_ = permitShrinkage;
    array_has_grown_ = false;//array has not grown yet
  }


  /*
    A service method to deal w/ a user-inputted inital array capacity.
  */
  private final int initCapacity(int initialCapacity)
    throws IllegalArgumentException{
      if (initialCapacity > MAX_CAPACITY){
	throw new IllegalArgumentException("initialCapacity must be no greater"
					   + " than 2^30");
      }
      else{
	// approximate initialCapacity with the closest power of 2
	// greater than initialCapacity; this could be done more
	// efficiently with a binary search on an array storing all the
	// powers of 2 between 1 and 2^30
	int ic = 1;
	while (ic < initialCapacity)
	  ic <<= 1;
	return ic;
      }
  }
    


  /**
    * Returns an empty ArraySequence.
    * O(1) time.
    */
  public Container newContainer(){
    return new ArraySequence(init_cap_, permit_shrinkage_);
  }

  
  /**
    * O(1) time.
    */
  public Position first() throws EmptyContainerException{
    checkEmpty();
    return positions_[first_];
  }


  /**
    * O(1) time.
    */
  public Position last() throws EmptyContainerException {
    checkEmpty();
    // Use modulo arithmetic. But add array_size_ first, because the -1
    // in this expression could result in an array index of -1 (illegal)
    int lastIndex = (first_+size_-1+array_size_)%array_size_;
    return positions_[lastIndex];
  }


  /**
    * O(1) time.
    */
  public boolean isFirst (Position p) throws InvalidAccessorException{
    // check that p != null, and that p is contained in this Sequence
    verifyContained(p); // throws IAE if null or from another container
    return p == positions_[first_];
  }


  /**
    * O(1) time.
    */
  public boolean isLast (Position p) throws InvalidAccessorException{
    // check that p != null, and that p is contained in this Sequence
    verifyContained(p); // throws IAE if null or from another container

    // Use modulo arithmetic. But add array_size_ first, because the -1
    // in this expression could result in an array index of -1 (illegal)
    int lastIndex = (first_+size_-1+array_size_)%array_size_;
    return p == positions_[lastIndex];
  }


  /**
    * O(1) time.
    */
  public Position atRank (int rank) throws BoundaryViolationException{
    if (rank<0 || rank>=size_){
      throw new BoundaryViolationException("Invalid rank.");
    }
    return positions_[(first_+rank)%array_size_];
  }


  /**
    * O(1) time.
    */
  public int rankOf (Position p) throws InvalidAccessorException{

    ArrayPos apos = verifyContained(p); // thows IAE if p is null,
    // or if p is not contained in this Sequence. Also converts to ArrayPos

    return apos.rank();
  }


  /**
    * O(1) time.
    */
  public Position before (Position p) throws 
    InvalidAccessorException, BoundaryViolationException{ 

      ArrayPos apos = verifyContained(p);// thows IAE if p is null,
      // or if p is not contained in this Sequence. Also converts to ArrayPos

      int rank = apos.rank()-1;
      if (rank<0)
	throw new BoundaryViolationException("Can't get before of first");

      return positions_[(first_+rank)%array_size_];
  }


  /**
    * O(1) time.
    */
  public Position after (Position p) throws
    InvalidAccessorException, BoundaryViolationException{

      ArrayPos apos = verifyContained(p);// thows IAE if p is null,
      // or if p is not contained in this Sequence. Also converts to ArrayPos

      int rank = apos.rank() + 1;
      if (rank>=size_)
	throw new BoundaryViolationException("Can't get after of last");

      return positions_[(first_+rank)%array_size_];
  }


  /**
    * This method also clears the Position and element caches.
    * O(n) time, where n is the number of elements in the Sequence.
    * In fact, at most n/2 Positions are shifted in one execution of 
    * insertBefore(p,elt).
    */
  public Position insertBefore (Position p, Object elt)
    throws InvalidAccessorException{ 
      return insertAtRank(rankOf(p), elt);
  }



  /**
    * This method also clears the Position and element caches.
    * O(n) time.
    * In fact, at most n/2 Positions will be shiften in one execution of
    * insertAfter(p,elt).
    */
  public Position insertAfter (Position p, Object elt)
    throws InvalidAccessorException{
      return insertAtRank(rankOf(p)+1, elt);
  }


  /**
    * This method also clears the Position and element caches.
    * O(1) time in the general case.
    * O(n) time if the array size must be doubled because of overflow.
    */
  public Position insertFirst(Object elt) throws InvalidAccessorException{
    return insertAtRank(0, elt);
  } 


  /**
    * This method also clears the Position and element caches.
    * O(1) time in the general case.
    * O(n) time if the array size must be doubled because of overflow.
    */
  public Position insertLast(Object elt)
    throws InvalidAccessorException{
      return insertAtRank(size(), elt);
  }


  /**
    * This method also clears the Position and element caches.
    * O(1) time if rank==0 or rank==size_, except in overflow cases.
    * O(n) time in the general case.
    */
  public Position insertAtRank (int rank, Object elt)
    throws InvalidAccessorException, BoundaryViolationException{
      ArrayPos apos = new ArrayPos(elt);
      if (rank<0 || rank>size_){
	throw new BoundaryViolationException("Invalid rank");
      }
      safePosInsertAtRank(rank, apos);
      return apos;
  }


  /**
    * Makes toInsert the first Position of this Sequence.
    * @param toInsert Position of a compatible type for this Sequence
    * @exception InvalidAccessorException if toInsert is already contained,
    * or is of an incompatible type, or is null
    * This method also clears the Position and element caches.
    * O(1) time in the general case.
    * O(n) time if the array size must be doubled because of overflow.
    */
  public void posInsertFirst( Position toInsert ) 
    throws InvalidAccessorException{
      posInsertAtRank(0, toInsert);
  }


  /**
    * Makes toInsert the last Position of this Sequence.
    * @param toInsert Position of a compatible type for this Sequence
    * @exception InvalidAccessorException if toInsert is already contained,
    * or is of an incompatible type, or is null
    * This method also clears the Position and element caches.
    * O(1) time in the general case.
    * O(n) time if the array size must be doubled because of overflow.
    */
  public void posInsertLast( Position toInsert ) 
    throws InvalidAccessorException{
      posInsertAtRank(size_, toInsert);
  }


  /**
    * Makes toInsert the predecessor of willBeSuccessor.
    * @param willBeSuccessor a Position in this Sequence
    * @param toInsert Position of a compatible type for this Sequence
    * @exception InvalidAccessorException if toInsert is already contained,
    * or is of an incompatible type, or is null; or if willBeSuccessor is 
    * null, incompatible, or not contained
    * This method also clears the Position and element caches.
    * O(n) time.
    */
  public void posInsertBefore( Position willBeSuccessor, Position toInsert ) 
    throws InvalidAccessorException{
      posInsertAtRank(rankOf(willBeSuccessor), toInsert);
  }


  /**
    * Makes toInsert the predecessor of willBeSuccessor.
    * @param willBePredecessor a Position in this Sequence
    * @param toInsert Position of a compatible type for this Sequence
    * @exception InvalidAccessorException if toInsert is already contained,
    * or is of an incompatible type, or is null; or if willBePredecessor is 
    * null, incompatible, or not contained
    * This method also clears the Position and element caches.
    * O(n) time.
    */
  public void posInsertAfter( Position willBePredecessor, Position toInsert ) 
    throws InvalidAccessorException{    
      posInsertAtRank(rankOf(willBePredecessor) + 1, toInsert);
  }


  /**
    * Makes toInsert to rank'th Position in this Sequence.
    * @param rank for n the size of this Sequence, rank must be in [0,n]
    * @param toInsert Position of a compatible type for this Sequence
    * @exception InvalidAccessorException if toInsert is already contained,
    * or is of an incompatible type, or is null
    * This method also clears the Position and element caches.
    * O(1) time if rank==0 or rank==size_ and no array overflow occurs.
    * O(n) time otherwise.
    */
  public void posInsertAtRank( int rank, Position toInsert )
    throws InvalidAccessorException{
      
      ArrayPos apos = verifyUncontained(toInsert);

      if (rank<0 || rank>size_){
	throw new BoundaryViolationException("Rank " +rank+ " out of bounds.");
      }
      safePosInsertAtRank(rank, apos);
  }


  /**
    * This method also clears the Position and element caches.
    * O(1) time if p is first or last, and no shrinkage of the array is needed.
    * O(n) otherwise.
    */
  public Object remove(Position p) throws InvalidAccessorException{
    ArrayPos apos = verifyContained(p);
    int removedRank = apos.rank();
    Object toReturn = apos.element();

    apos.setContainer(null);//Position now knows it's out of this Container
    apos.setRank(-1);//just for safety -- we want its rank to be unusable

    if (removedRank>(size_/2)){//if removed pos is nearer the end
      //move last part of the sequence
      shiftPositionsMinusOne(removedRank+1, size_-1);
      //downshifts Positions in array
    }
    
    else{// removed pos is nearer the front 
      //move front part of sequence
      shiftPositionsPlusOne(0, removedRank-1);
      //shifts Positions 1 index forward 
      first_ = (first_+1)%array_size_;//adjust the first_ index
    }

    size_--;
      
    //now reset the rank of all Positions at ranks higher than removed pos
    for (int j=removedRank; j<size_; j++){
      positions_[(first_+j)%array_size_].setRank(j);//update rank
    }

    //clear out the caches
    cPos_ = null;
    cElts_ = null;

    ensureLoadFactor();//shrink the array if load factor is too low

    return toReturn;
  }


  /**
    * This method also clears the Position and element caches.
    * O(n) time.
    */
  public Object removeAfter(Position p) throws
    InvalidAccessorException, BoundaryViolationException{
    return remove(after(p));
  }


  /**
    * This method also clears the Position and element caches.
    * O(n) time.
    */
  public Object removeBefore(Position p) throws
    InvalidAccessorException, BoundaryViolationException {
    return remove(before(p));
  }


  /**
    * This method also clears the Position and element caches.
    * O(1) time, except in cases where the array size must be halved, to 
    * maintain a load factor of at least 0.25.
    */
  public Object removeFirst() throws EmptyContainerException {
    checkEmpty();
    return remove(first());
  }


  /**
    * This method also clears the Position and element caches.
    * O(1) time, except in cases where the array size must be halved, to 
    * maintain a load factor of at least 0.25.
    */
  public Object removeLast() throws EmptyContainerException {
    checkEmpty();
    return remove(last());
  }


  /**
    * This method also clears the Position and element caches.
    * O(n) time.
    */
  public Object removeAtRank(int i) throws BoundaryViolationException {
    return remove(atRank(i));
  }


  /**
    * O(1) time.
    */
  public int size() {
    return size_;
  } 


  /**
    * This method also invalidates the elements cache.
    * O(1) time.
    */
  public Object replaceElement(Accessor a, Object newElement) 
    throws InvalidAccessorException{
      
      ArrayPos apos = verifyContained(a);// checks that a is not null,
      // and that it is an ArrayPos contained in this Sequence.
      // Throws IAE otherwise.

      Object toReturn = apos.element();
      apos.setElement(newElement);

      //invalid the elements cache.  You can't change the element in the cache,
      //since that would change the values in existing iterators which are
      //currently in use.
      cElts_ = null;

      return toReturn;
  }


  /**
    * O(1) time if the cache already exitsts.
    * Otherwise O(n) time to construct it.
    */
  public PositionIterator positions(){
    //if cache is invalid, create it
    if (cPos_ == null){
      cPos_ = new Position[size_];
      circularPositionsArrayCopy(cPos_);
    }
    return new ArrayPositionIterator(cPos_);
  }



  /**
    * O(1) time if the cache already exists.
    * Otherwise O(n) time to construct it.
    */
  public ObjectIterator elements(){
    //if cache is invalid, but there is a Positions cache, then create it from
    //the Positions cache.  Otherwise iterate through the sequence, and get all
    //the Positions.
    if( cElts_ == null ){
      cElts_ = new Object[size_];
      if( cPos_ != null ){
	for ( int i = 0 ; i < cElts_.length; ++i ){
	  cElts_[i] = cPos_[i].element();
	}
      }
      else{
	for (int i=0; i<size_; i++){
	  cElts_[i] = positions_[(first_+i)%array_size_].element();
	}
      }
    }
    return new ArrayObjectIterator(cElts_);
  }



  /**
    * O(1) time.
    */
  public boolean contains(Accessor a) throws InvalidAccessorException{
    if (a == null){
      throw new InvalidAccessorException("null accessor");
    }
    ArrayPos apos;
    try{
      apos = (ArrayPos)a;
    }
    catch(ClassCastException cce){
      return false;
    }
    return (apos.container() == this);
  }



  /**
    * O(n) time.
    */
  public String toString(){
    return ToString.stringfor(this);
  }


  /**
    * A public convenience method that allows the user to 
    * toggle the shrinkability of the array.
    * O(1) time.
    */
  public void setArrayShrinkability(boolean permitShrinkage){
    permit_shrinkage_ = permitShrinkage;
  }



  //*************Auxillary methods************************


  /* 
     Makes sure the array is large enough; if not, double the capacity.
   */
  private final void ensureCapacity(){
    if (size_ >= positions_.length){//if array needs to grow
      if (size_ > MAX_CAPACITY/2){
	throw new FullContainerException("Maximum capacity of the Sequence exceeded.");
      }
      //reallocate array to twice its current size
      ArrayPos[] p2 = new ArrayPos[positions_.length*2];
      circularPositionsArrayCopy(p2);
      array_size_ = positions_.length*2;
      first_ = 0;
      positions_ = p2;
      array_has_grown_ = true;
    }
  }

  /* 
     Makes sure the load factor of the array is greater than
     SHRINK_LOAD_FACTOR; if not, halve the capacity.
  */
  private final void ensureLoadFactor(){
    if (permit_shrinkage_ &&
	array_has_grown_ &&
	size_ <= positions_.length/SHRINK_LOAD_FACTOR &&
	positions_.length >= 2*init_cap_){
      // halve the array capacity
      ArrayPos[] p2 = new ArrayPos[positions_.length/2];
      circularPositionsArrayCopy(p2);
      array_size_ = positions_.length/2;
      first_ = 0;
      positions_ = p2;
    }
  }



  /*
    Copies all Positions from the original array into second array passed
    in. Uses system.arraycopy method, but must first divide original array
    into two portions to deal w/ wraparound property.
    
    Assume that array2 is big enough, which should be the case if nothing is
    broken.
   */
  private final void circularPositionsArrayCopy(Position[] array2){ 

    // if there are no Positions in the Sequence, then nothing to copy
    if (size_ == 0){
      return;
    }

    // find out how many indices from first Pos to end of array (inclusive)
    int numberFromFirst = array_size_ - first_;
    
    // if this number >= size_ then no wrapping required, so do basic copy
    if (numberFromFirst >= size_){
      System.arraycopy(positions_, first_, array2, 0, size_);
    }
    else{// wrapping is required
      //first copy the portion starting at positions_[first_]
      System.arraycopy(positions_, first_, array2, 0, numberFromFirst);
      //now copy the last portion of the Seq (which starts at positions_[0])
      System.arraycopy(positions_, 0, array2, numberFromFirst,
		       size_ - numberFromFirst);
    }
  }



  /*
    Shift all Positions between rank1 and rank2 (inclusive) to be 
    one index lower in the array.
  */
  private final void shiftPositionsMinusOne(int rank1, int rank2){

    // number of Positions to shift
    int numToShift = rank2 - rank1 + 1;

    if (numToShift == 0){
      return;
    }

    int pos1Index = (first_+rank1)%array_size_;
    int pos2Index = (first_+rank2)%array_size_;

    int newPos1Index = (pos1Index-1+array_size_)%array_size_;

    // if it's an easy case, where we can do it in one chunk....
    if (pos2Index >= pos1Index &&
	pos1Index > 0){
      System.arraycopy(positions_, pos1Index, positions_, newPos1Index, numToShift);
    }

    else{//we have to copy the Sequence in parts, because of the wrap-around
      
      // find out how many indices from first Pos to end of array (inclusive)
      int numberFromFirst = (array_size_ - pos1Index)%array_size_;

      // System.out.println("numberFromFirst = " + numberFromFirst);
//       System.out.println("pos1Index = " + pos1Index);
//       System.out.println("pos2Index = " + pos2Index);
//       System.out.println("newPos1Index = " + newPos1Index);


      // copy the portion of the Seq starting at positions_[pos1Index]
      System.arraycopy(positions_, pos1Index, positions_, newPos1Index,
		       numberFromFirst);

      // now move a lone Position from beginning of array to end
      positions_[array_size_-1] = positions_[0];

      // now move the portion of the Seq starting at positions_[1]
      int numLeftToMove = numToShift - numberFromFirst - 1;
      System.arraycopy(positions_, 1, positions_, 0, numLeftToMove);
    }

    // ** This chunk of code is what the above madness replaced
    // for (int i=rank1; i<=rank2; i++){
    //       int oldIndex = (first_+i)%array_size_;
    //       int newIndex = (oldIndex-1+array_size_)%arraySize;// = oldIndex-1
    //       positions_[newIndex] = positions_[oldIndex];
    // }
    // ** end old chunk of code
    // I am keeping it here in case we find out that the compiler can do this
    // sort of thing more efficiently than we can by hand.

    //now clean out the last space (maybe unnecessary, but good for memory)
    int lastIndex = (first_+rank2)%array_size_;
    positions_[lastIndex] = null;
  }



  /*
    Shift all Positions between rank1 and rank2 (inclusive) to be one
    index higher in the array.
  */
  private final void shiftPositionsPlusOne(int rank1, int rank2){

    //number of Positions to shift
    int numToShift = rank2 - rank1 + 1;

    if (numToShift == 0){
      return;
    }

    int pos1Index = (first_+rank1)%array_size_;
    int pos2Index = (first_+rank2)%array_size_;

    int newPos1Index = (pos1Index+1)%array_size_;

    // if it's an easy case, where we can do it in one chunk...
    if (pos2Index >= pos1Index && 
	pos2Index < array_size_-1){// last Pos won't fall off end of array
      System.arraycopy(positions_, pos1Index, positions_, newPos1Index,
		       numToShift);
    }

    else{//we have to copy the Sequence in parts, because of the wrap-around
      
      // find out how many indices from beginning of array to rank2 pos (inclusive)
      int numAtFront = (pos2Index + 1)%array_size_;
      
     //  System.out.println("numAtFront = " + numAtFront);
//       System.out.println("pos1Index = " + pos1Index);
//       System.out.println("pos2Index = " + pos2Index);
//       System.out.println("newPos1Index = " + newPos1Index);

      // copy portion of array starting at positions_[0]
      System.arraycopy(positions_, 0, positions_, 1, numAtFront);

      // now move a lone Position from end of array to beginning
      positions_[0] = positions_[array_size_-1];

      // now move the portion of the array starting at rank1 pos
      int numLeftToMove = numToShift - 1 - numAtFront;
      System.arraycopy(positions_, pos1Index, positions_, newPos1Index, 
		       numLeftToMove);
    }

    // ** This chunk of code is what the above madness replaced
    //  for (int i=rank2; i>=rank1; i--){
    //       int oldIndex = (first_+i)%array_size_;
    //       int newIndex = (oldIndex+1)%array_size_;
    //       positions_[newIndex] = positions_[oldIndex];
    //  }
    // ** end old chunk of code
    // I am keeping it here in case we find out that the compiler can do this
    // sort of thing more efficiently than we can by hand.

    //now clean out the first space (maybe unnecessary, but good for memory)
    int firstIndex = (first_+rank1)%array_size_;
    positions_[firstIndex] = null;
  }



  /*
    Checks for null, and attempts to cast a Position to an ArrayPos.
  */
  private final ArrayPos castPosition(Accessor a) throws
    InvalidAccessorException{

    if (a==null)
      throw new InvalidAccessorException("null accessor");

    ArrayPos apos;
    try{
      apos = (ArrayPos)a;
    }
    catch (ClassCastException cce){
      throw new InvalidAccessorException("Wrong class " + a.getClass());
    }
    
    return apos;
  }



  private final void checkEmpty() throws EmptyContainerException{
    if (isEmpty())
      throw new EmptyContainerException("Sequence is empty");
  }



  /*
    This helper method should be used only when 
    1. The Position has already been cast successfully to an ArrayPos.
    2. The ArrayPos is not null.
    3. The speicified rank is within bounds.
    4. the ArrayPos is not already contained by this container.
  */
  private final void safePosInsertAtRank(int rank, ArrayPos apos){
       
    ensureCapacity();//ensures array is large enough; if not, doubles capacity

    if (isEmpty()){
      safePosInsertOnly(apos);
      return;
    }

    if (rank>(size_/2)){//if rank is nearer to the end of the sequence
      //move everything after rank up one index
      shiftPositionsPlusOne(rank, size_-1);
    }
    else{// rank is in first half of sequence
      //move front part of the sequence
      shiftPositionsMinusOne(0, rank-1);

      // adjust first_ index
      // Use modulo arithmetic. But add array_size_ first, because the -1
      // in this expression could result in an array index of -1 (illegal)
      first_ = (first_-1+array_size_)%array_size_;
    }
    
    //now stick the new Position in proper rank/index
    positions_[(first_+rank)%array_size_] = apos;
    apos.setRank(rank);
    apos.setContainer(this);

    size_++;

    //clear the caches
    cPos_ = null;
    cElts_ = null;

    //adjust the ranks of all Positions at ranks higher than the added pos
    for (int j=rank+1; j<size_; j++){
      positions_[(first_+j)%array_size_].setRank(j);
    }
  }



  private final void safePosInsertOnly(ArrayPos apos){
    positions_[0] = apos;
    apos.setRank(0);
    apos.setContainer(this);
    size_ = 1;
    first_ = 0;

    //invalidate the caches
    cPos_ = null;
    cElts_ = null;
  }

  

  /*
    Verifies that pos is contained by this container, and casts it to ArrayPos.
    Also ensures that pos is not null.
  */
  private final ArrayPos verifyContained(Accessor pos) throws
    InvalidAccessorException{
    ArrayPos apos = castPosition(pos);
    if (apos.container() != this){
      throw new InvalidAccessorException("Position not contained by this Sequence");
    }
    return apos;
  }



  /*
    Verifies that pos is _not_ contained by this, and casts it to an ArrayPos.
    Also ensures that pos is not null.
  */
  private final ArrayPos verifyUncontained(Accessor pos) throws
    InvalidAccessorException{
    ArrayPos apos = castPosition(pos);
    if (apos.container() == this){
      throw new InvalidAccessorException("Position is already contained by this Sequence");
    }
    return apos;
  }
  


  /**
    * This nested class is the Position for ArraySequence.
    * It is Decorable, and a Position.
    */

  private static class ArrayPos extends HashtableDecorable
    implements Position {


    /**
      * The container that this ArrayPos belongs to.
      * (This makes O(1) calls to contains() possible)
      */
    private InspectableContainer cont_;

    /** 
      * This ArrayPos's rank in the Sequence.
      */
    private int rank_;

    /**
      * The element this Position stores
      */
    private Object elt_;


    /**
      * Constructor for the ArrayPos.
      * @param elt The Position's element.
      */
    ArrayPos(Object elt){
      elt_ = elt;
    }


    public final Object element(){
      return elt_;
    }


    public String toString(){
      return ToString.stringfor(this);
    }


    /**
      * Gets the Position's container, for O(1) implementation of contains()
      * @return The Position's container
      */
    final InspectableContainer container(){
      return cont_;
    }


    /**
      * Sets the Position's container, for O(1) implementation of contains()
      * @param c The Position's container
      */
    final void setContainer(InspectableContainer c){
      cont_ = c;
    }


    /**
      * Sets the Position's element
      * @param elt The Position's new element
      */
    final void setElement(Object elt){
      elt_ = elt;
    }

    
    /**
      * Gets the Position's rank in the Sequence.
      */
    final int rank(){
      return rank_;
    }


    /**
      * Sets the Position's rank in the Sequence.
      * @param rank The Position's new rank.
      */
    final void setRank(int rank){
      rank_ = rank;
    }
  }


}

    
