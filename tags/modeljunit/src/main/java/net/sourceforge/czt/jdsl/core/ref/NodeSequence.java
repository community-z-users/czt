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
 * A Sequence based on a doubly-linked-list implementation.<p>
 *
 * It incorporates the iterator caching optimization:<br>
 * calls to iterator() are amortized
 * O(n/k) time if called k times between modifications of the sequence.
 * This is accomplished by making a list of
 * the positions of the sequence whenever iterating through
 * the list is necessary, and using it until there is a modification
 * to the Sequence. <p>
 *
 * This implementation does not use fictitious positions at the
 * beginning or end of the Sequence, and the head and tail node have
 * null pointers past the beginning or end of the Sequence. <p>
 *
 * The non-interface methods for inserting positions are implemented
 * separately in order to allow greater constant-factor efficiency
 * and comprehensibility in
 * the Sequence insertion methods and to allow later separation of their
 * functionality.
 * @author Benoit Hudson
 * @author Mark Handy
 * @author Andrew Schwerin
 * @author Ryan Shaun Baker
 * @version JDSL 2.1.1 
 */
public class NodeSequence extends AbstractPositionalContainer 
  implements Sequence {


  /**
    * The stored size of the Sequence -- modified on insertion or removal.
    */
    private int size_;

  /**
    * The first and last nodes of the Sequence
    */
    private FNSNode tail_, head_;

  /**
    * Cache for positions and elements; discarded upon modification
    */
    private Position positions_[] = null;
    private Object elements_[] = null;


  /**
    * The default constructor for NodeSequence, as well as the only one.
    */
    public NodeSequence() {
        super();
    }
    public Container newContainer() {
        return new NodeSequence();
    }

   
  /**
    * O(1) time
    */
    public Position first() throws EmptyContainerException {
        checkEmpty();
        return head_;
    }

  /**
    * O(1) time
    */
    public Position last() throws EmptyContainerException {
        checkEmpty();
        return tail_;
    }


  /**
    * O(1) time
    */
    public boolean isFirst (Position p) throws InvalidAccessorException {
        castPosition (p);
        return (p==head_);
    }

  /**
    * O(1) time
    */
    public boolean isLast (Position p) throws InvalidAccessorException  {
        castPosition (p);
        return (p==tail_);
    }

  /**
    * O(1) time if the positions_ cache is valid (no modifications since
    * cache was generated)
    * O(N) if cache is invalid (must traverse up to half of Sequence)
    */
    public Position atRank (int rank) throws BoundaryViolationException {
        checkRank (rank);

        // if the positions_ cache is valid, we can return in O(1) time
        if(positions_!=null) {
            return positions_[rank];
        }

        // otherwise, iterate through the list
        else {
	  //we save half of N by going from the appropriate end
	  if (rank<=size()/2){
            FNSNode cur = head_;
            for(int i=0; i<rank; i++)  {
                cur = cur.next();
            }
            return cur;
	  }
	  else{
            FNSNode cur = tail_;
            for(int i=size()-1; i>rank; i--)  {
                cur = cur.prev();
            }
            return cur;
	  }
	    
        }
    }

  /**
    * O(1) time if the positions_ cache is valid (no modifications since
    * cache was generated)
    * O(N) if cache is invalid (must traverse rank elements of Sequence)
    */ 
    public int rankOf (Position p) throws InvalidAccessorException {
        FNSNode n = castPosition(p);

        // if the positions_ cache is valid, we can iterate through an array
        if(positions_!=null) {
            for(int i=0; i<positions_.length; i++) {
                if(positions_[i]==p) return i;
            }
            // to placate the compiler:
            throw new RuntimeException
                ("Internal error: "+p+" is valid but not found");
        } else {
            // otherwise, iterate through the list (backwards)
            int rank=0;
            while(n!=head_) { rank++; n = n.prev(); }
            return rank;
        }
    }    

  /**
    * O(1) time
    */
    public Position before (Position p) throws InvalidAccessorException { 
      FNSNode n = castPosition(p);
      if(n==head_) 
	throw new BoundaryViolationException("At first element");
      return n.prev();
    }

  /**
    * O(1) time
    */
    public Position after (Position p) throws InvalidAccessorException {
      FNSNode n = castPosition(p);
      if(n==tail_) 
	throw new BoundaryViolationException("At last element");
      return n.next();
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Position insertBefore (Position p, Object elt)
                                  throws InvalidAccessorException  { 
	Position nu = new FNSNode(elt);
	posInsertBefore(p, nu);
        return nu;
    } 

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Position insertFirst(Object elt) throws InvalidAccessorException {
  	Position nu = new FNSNode(elt);
	if (isEmpty())
	  posInsertOnly(nu);
	else
	  posInsertBefore(head_, nu);
        return nu; 
    } 

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Position insertAfter (Position p, Object elt)
        throws InvalidAccessorException {
	  Position nu = new FNSNode(elt);
	  posInsertAfter(p, nu);
	  return nu;
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Position insertLast(Object elt)
        throws InvalidAccessorException {
	  Position nu = new FNSNode(elt);
	  if (isEmpty())
	    posInsertOnly(nu);
	  else
	    posInsertAfter(tail_, nu);
	  return nu; 
        }

   /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Position insertAtRank (int rank, Object elt)
           throws InvalidAccessorException, BoundaryViolationException  {
        if (rank == 0)      { return insertFirst(elt); }
        if (rank == size()) { return insertLast (elt); }
        checkRank (rank);
        return insertAfter(atRank(rank-1),elt);
    }

  /**
    * This method inserts a position into an empty Sequence.
    * It also clears the position cache
    * @param toInsert The Position to Insert
    * O(1) time
    */
  private void posInsertOnly(Position toInsert) 
                              throws InvalidAccessorException{
    try{
      FNSNode toins = (FNSNode)toInsert;
      head_ = toins;
      tail_ = toins;
      size_ = 1;
      toins.setContainer(this);
      toins.setPrev(null);
      toins.setNext(null);
      positions_ = null;
      elements_ = null;
    }
    catch(ClassCastException cce){
      throw new InvalidAccessorException
	("Wrong class " + toInsert.getClass() );
    }
  }


   /**
 * Make toInsert the first position of this sequence
 * @param toInsert Position of a compatible type for this sequence
 * @exception InvalidAccessorException If toInsert is already
 * contained or is of an incompatible type
    * This method also clears the position cache.
    * O(1) time
    */
  public void posInsertFirst( Position toInsert ) 
                              throws InvalidAccessorException {
    if (isEmpty())
      posInsertOnly(toInsert);
    else
      posInsertBefore(head_, toInsert);
  }

  /**
 * Make toInsert the last position of this sequence
 * @param toInsert Position of a compatible type for this sequence
 * @exception InvalidAccessorException If toInsert is already
 * contained or is of an incompatible type
    * This method also clears the position cache.
    * O(1) time
    */
  public void posInsertLast( Position toInsert ) 
                             throws InvalidAccessorException {
    if (isEmpty())
      posInsertOnly(toInsert);
    else
      posInsertAfter(tail_, toInsert);
  }

  /**
 * Make toInsert the predecessor of willBeSuccessor
 * @param willBeSuccessor a position in this sequence
 * @param toInsert Position of a compatible type for this sequence
 * @exception InvalidAccessorException If toInsert is already
 * contained or is of an incompatible type, or if willBeSuccessor
 * is invalid for one of the usual invalid-position reasons
    * This method also clears the position cache.
    * O(1) time
    */
  public void posInsertBefore( Position willBeSuccessor, Position toInsert ) 
                               throws InvalidAccessorException {

    if (contains(toInsert))
      throw new InvalidAccessorException
	("This container already contains that position.");

    // clear the caches
    positions_= null;
    elements_= null;
    
    FNSNode fwillbesucc = castPosition(willBeSuccessor);
    FNSNode ftoInsert = null;
    
    //we can't use castPosition because it SHOULD BE uncontained
    try{
      ftoInsert = (FNSNode)toInsert;
    }
    catch(ClassCastException cce){
      throw new InvalidAccessorException
	("Node to insert is of the wrong class.");
    }
    
    if(fwillbesucc==head_) { //We're de-facto inserting first
      ftoInsert.setPrev(null);
      ftoInsert.setNext(fwillbesucc);
      ftoInsert.setContainer(this);
      
      fwillbesucc.setPrev(ftoInsert);

      head_ = ftoInsert;
      if(tail_ == null) 
	tail_ = head_;
    } else {//inserting somewhere in the middle
      ftoInsert.setPrev(fwillbesucc.prev());
      fwillbesucc.prev().setNext(ftoInsert);
      ftoInsert.setNext(fwillbesucc);
      fwillbesucc.setPrev(ftoInsert);
      ftoInsert.setContainer(this);
    }
    size_++;
  }
  
  /**
 * Make toInsert the successor of willBePredecessor
 * @param willBePredecessor a position in this sequence
 * @param toInsert Position of a compatible type for this sequence
 * @exception InvalidAccessorException If toInsert is already
 * contained or is of an incompatible type, or if willBePredecessor
 * is invalid for one of the usual invalid-position reasons
    * This method also clears the position cache.
    * O(1) time
    */
  public void posInsertAfter( Position willBePredecessor, Position toInsert ) 
                              throws InvalidAccessorException {    
    if (contains(toInsert))
      throw new InvalidAccessorException
	("This container already contains that position.");

    // clear the caches
    positions_= null;
    elements_= null;
    
    FNSNode fwillbepred = castPosition(willBePredecessor);
    FNSNode ftoInsert=null;
    
    //we can't use castPosition because it SHOULD BE uncontained
    try{
      ftoInsert = (FNSNode)toInsert;
    }
    catch(ClassCastException cce){
      throw new InvalidAccessorException
	("Node to insert is of the wrong class.");
    }
    
    if(fwillbepred==tail_) { //We're de-facto inserting last
      ftoInsert.setNext(null);
      ftoInsert.setPrev(fwillbepred);
      ftoInsert.setContainer(this);
      
      fwillbepred.setNext(ftoInsert);

      tail_ = ftoInsert;
      if(head_ == null) 
	head_ = tail_;
    } else {//inserting somewhere in the middle
      ftoInsert.setNext(fwillbepred.next());
      fwillbepred.next().setPrev(ftoInsert);
      ftoInsert.setPrev(fwillbepred);
      fwillbepred.setNext(ftoInsert);
      ftoInsert.setContainer(this);
    }
    size_++;
  }

  /**
 * Make toInsert the rank'th position in this sequence
 * @param rank for n the size of this sequence, rank must be in [0,n]
 * @param toInsert Position of a compatible type for this sequence
 * @exception InvalidAccessorException If toInsert is already
 * contained or is of an incompatible type
    * This method also clears the position cache.
    * O(1) time
    */
  public void posInsertAtRank( int rank, Position toInsert )
                               throws InvalidAccessorException {
    if (contains(toInsert))
      throw new InvalidAccessorException
	("This container already contains that position.");

    if (rank == 0)      { posInsertFirst(toInsert);return;}
    if (rank == size()) { posInsertLast (toInsert);return; }
    checkRank (rank);
    FNSNode n = (FNSNode)atRank(rank-1);
    posInsertAfter(n,toInsert);
  }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Object remove (Position p) throws InvalidAccessorException {
        FNSNode n = castPosition(p);
          FNSNode prev = n.prev();
        FNSNode next = n.next();

        // clear the cache
        positions_ = null;
	elements_ = null;

        Object retval = n.element();
        n.setContainer(null);

        // skip over the position we're removing.
        if(prev!=null) {
            prev.setNext(next);
        } else {
            head_ = next;
        }
        if(next!=null) {
            next.setPrev(prev);
        } else {
            tail_ = prev;
        }

        size_--;
        return retval;
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Object removeAfter(Position p) throws InvalidAccessorException {
        return remove(after(p));
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Object removeBefore(Position p) throws InvalidAccessorException {
        return remove(before(p));
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Object removeFirst() throws InvalidAccessorException {
        return remove(first());
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Object removeLast() throws InvalidAccessorException {
        return remove(last());
    }

  /**
    * This method also clears the position cache.
    * O(1) time
    */
    public Object removeAtRank(int i) throws InvalidAccessorException {
        return remove(atRank(i));
    }

  /**
    * O(1) time
    */
    public int size() {
        return size_;
    }
 
  /**
    * O(1) time
    */
  public Object replaceElement(Accessor a, Object newElement) 
                               throws InvalidAccessorException {
				 
    //clear the elements but not the positions cache
    elements_ = null;			
    FNSNode afns = castPosition(a);
    Object retval = afns.element();
    afns.setElement(newElement);
    return retval;
  }

  /**
    * O(1) time if the cache already exists
    * Otherwise O(N) to construct it
    */
  public PositionIterator positions(){
        // if the cache is invalid, create it
        if(positions_ == null) {
            positions_ = new Position[size_];
            FNSNode cur = head_;
            for(int i=0; i<size_; i++) {
                positions_[i] = cur;
                cur = cur.next();
            }
        }
        return new ArrayPositionIterator(positions_);
  }

  /**
    * O(1) time if the cache already exists
    * Otherwise O(N) to construct it
    */
  public ObjectIterator elements(){
        // if the cache is invalid, create it
        if(elements_ == null) {
            elements_ = new Object[size_];
            FNSNode cur = head_;
            for(int i=0; i<size_; i++) {
                elements_[i] = cur.element();
                cur = cur.next();
            }
        }
        return new ArrayObjectIterator(elements_);
  }

  /**
    * O(1) time
    */
  public boolean contains(Accessor a) throws InvalidAccessorException {
    if (a == null)
      throw new InvalidAccessorException
	("A null position cannot be contained.");
    else if (a instanceof FNSNode)
      return ((FNSNode)a).container() == this;
    else
      return false;
  }
  
  public String toString(){  
    return ToString.stringfor(this);
  }

    // Convenience methods

  /**
    * This method throws an exception if the Sequence is empty.
    * O(1) time
    */
    private final void checkEmpty() 
        throws EmptyContainerException {
            if(isEmpty()) throw new EmptyContainerException 
			    ("Sequence is empty");
        }

  /**
    * This method throws an exception if the rank is out of bounds
    * @param rank The rank to check
    * O(1) time
    */
    private final void checkRank(int rank) 
        throws BoundaryViolationException {
            if (rank < 0 || rank >= size_) throw new BoundaryViolationException
                ("Rank " +rank+ " out of range [0.."+size_+")");
        }								

  /**
    * This method throws an exception if the position is 
    * not a non-null FNSNode contained by this.
    * @param a The accessor to check
    * O(1) time
    */
  private final FNSNode castPosition(Accessor a) 
    throws InvalidAccessorException {

    if (a==null)
      throw new InvalidAccessorException("null accessor");

    FNSNode n; 
    try{
      n = (FNSNode)a;
    }
    catch (ClassCastException cce) {
      throw new InvalidAccessorException("Wrong class " + a.getClass() );
    }
    
    if (n.container() != this)
      throw new InvalidAccessorException("wrong container");
    
    return n;
  }
    


    
    // ------------------------------------------------------


    
    /**
     * This nested class is the node for NodeSequence.
     * It is Decorable, and a position.  It is public per request of mdh,
     * who hacked with it in the low-overhead implementation of
     * Graph.
     */
    
    public static class FNSNode extends HashtableDecorable
    implements Position {
	
	/**
	 * The nodes immediately before and after this one (may be null
	 * if this node is at an end of the Sequence)
	 * @serial
	 */
        private FNSNode next_, prev_;
	
	/**
	 * The container that this node belongs to
	 * (this makes O(1) time calls to contains() possible)
	 * @serial
	 */
        private InspectableContainer cont_;
	
	/**
	 * The element this position stores
	 * @serial
	 */
        private Object  elt_;
	
	/**
	 * Constructor for the Node. 
	 * @param prev The node before this one in the Sequence. (may be null)
	 * @param next The node after this one in the Sequence. (may be null)
	 * @param cont The node's container. (may be null)
	 * @param elt The node's element. (null if the element is really null)
	 */
        private FNSNode(FNSNode prev, FNSNode next,
		InspectableContainer cont, Object elt) {
            prev_ = prev; if(prev!=null) prev.setNext(this);
            next_ = next; if(next!=null) next.setPrev(this);
            cont_ = cont;
            elt_ = elt;
        }

      /**
	 * Default constructor for the Node. 
	 * @param elt The node's element. (null if the element is really null)
	 */
      public FNSNode(Object elt){
	prev_ = null;
	next_ = null;
	cont_ = null;
	elt_ = elt;
      }
	
        public final Object element() { 
            return elt_;
        }

	/**
	 * Gets the node after this one in the Sequence
	 * @return The node after this one in the Sequence
	 */
        final FNSNode next() { return next_; }
	
	/**
	 * Gets the node before this one in the Sequence
	 * @return The node before this one in the Sequence
	 */
        final FNSNode prev() { return prev_; }
	
	/**
	 * Sets the node after this one in the Sequence
	 * @param n The node after this one in the Sequence
	 */
        private final void setNext(FNSNode n) { next_ = n; }
	
	/**
	 * Sets the node before this one in the Sequence
	 * @param p The node before this one in the Sequence
	 */
        private final void setPrev(FNSNode p) { prev_ = p; }
	
	/**
	 * Sets the position's element
	 * @param elt The position's new element
	 */
	protected final void setElement(Object elt) {
            elt_ = elt;
        }
	
	/**
	 * Gets the position's container, for O(1) time implementation of contains()
	 * @return The position's container
	 */
	final InspectableContainer container() {
	    return cont_;
	}
	
	/**
	 * Sets the position's container, for O(1) time implementation of contains()
	 * @param c The position's container
	 */
	final void setContainer(InspectableContainer c){
	    cont_ = c;
	}
	
	public String toString(){
	    return ToString.stringfor(this);
	}
    }

}

