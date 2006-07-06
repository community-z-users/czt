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
 * Please refer to the documentation of <code>Tree</code>
 *
 * @version JDSL 2.1.1 
 * @author Mike Boilen (mgb)
 * @author Andrew Schwerin (schwerin)
 * @author Luca Vismara (lv)
 * @author Galina Shubina (gs)
 * @see Tree
 */
public interface InspectableTree extends InspectablePositionalContainer {

  // query methods

  /** 
   * Checks if a position is the root of this tree.
   *
   * @param node a node
   * @return <code>true</code> if <code>node</code> is the root of this tree
   *
   * @exception InvalidAccessorException if <code>node</code> is null or
   * does not belong to this tree
   */
  public boolean isRoot (Position node) throws InvalidAccessorException;


  /** 
   * Checks if a position is an internal node of this tree.
   *
   * @param node a node
   * @return <code>true</code> if <code>node</code> has at least one child
   *
   * @exception InvalidAccessorException if <code>node</code> is null or
   * does not belong to this tree
   */
  public boolean isInternal (Position node) throws InvalidAccessorException;


  /** 
   * Checks if a position is a leaf of this tree.
   * 
   * @param node Any node of the tree
   * @return <code>true</code> if <code>node</code> has no children
   *
   * @exception InvalidAccessorException if <code>node</code> is null or
   * does not belong to this tree
   */
  public boolean isExternal (Position node) throws InvalidAccessorException;
  

  // accessor methods

  /**
   * Gets the root of this tree.
   *
   * @return The top node of the tree (may also be a leaf if the tree
   * has exactly one node)
   */
  public Position root();

  
  /**
   * Gets the parent of a given node.
   * 
   * @param node a node
   * @return parent position of the given node
   *
   * @exception BoundaryViolationException if <code>node</code> is the
   * root of the tree
   * @exception InvalidAccessorException if <code>node</code> is null or
   * does not belong to this tree
   */
  public Position parent (Position node) throws BoundaryViolationException,
  InvalidAccessorException;

  
  /** 
   * Returns an iterator over the children of the <code>node</code> in order.
   * If the <code>node</code> is a leaf, the iterator has no elements.  
   * The iterator returned is a snapshot -- it iterates over all positions 
   * that were children of node at the moment that children(.) was called, 
   * regardless of subsequent modifications to the container.
   *
   * @param node a node of the tree
   * @return iterator over all the children of node
   *
   * @exception InvalidAccessorException if <code>node</code> is null or
   * does not belong to this tree
   */
  public PositionIterator children (Position node) throws
  InvalidAccessorException;


  /** 
   * Returns an iterator over the siblings of the <i>node</i> in order.
   * in order. If the <code>node</code> has no siblings, the iterator
   * has no elements. The iterator returned is a snapshot --
   * it iterates over all positions that were siblings of <code>node</code>
   * at the moment that siblings(.) was called, regardless of subsequent
   * modifications to the container.
   *
   * @param node a node of the tree
   * @return iterator over all the other children of the same parent
   *
   * @exception BoundaryViolationException if <code>node</code> is the
   * root of the tree
   * @exception InvalidAccessorException if <code>node</code> is null or
   * does not belong to this tree
   */
  public PositionIterator siblings (Position node) throws
  BoundaryViolationException, InvalidAccessorException;


  /** 
   * @param node a node of the tree
   * @return the number of children of <code>node</code>
   *
   * @exception InvalidAccessorException if <code>node</code> is null or 
   * does not belong to this tree
   */
  public int numChildren (Position node) throws InvalidAccessorException;


  /**
   * @param node a node
   * @return the sibling after <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * either the last child of a node or the root
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position siblingAfter (Position node) throws
  BoundaryViolationException, InvalidAccessorException;


  /**
   * @param node a node
   * @param rank an integer index of the children of
   * <code>node</code>; childAtRank(0) is the first child,
   * childAtRank(numChildren(node)-1) is the last child
   * @return the child of <code>node</code> at the specified rank
   *
   * @exception BoundaryViolationException if rank < 0 or rank >
   * numChildren(node)-1 or node is a leaf
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position childAtRank (Position node, int rank) throws
  BoundaryViolationException, InvalidAccessorException;


  /**
   * @param node a node
   * @return the sibling before <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * either the first child of a node or the root
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position siblingBefore (Position node) throws
  BoundaryViolationException, InvalidAccessorException;


  /**
   * @param node a node
   * @return the first child of <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * a leaf
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position firstChild (Position node) throws
  BoundaryViolationException, InvalidAccessorException;


  /**
   * @param node a node
   * @return the last child of <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * a leaf
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position lastChild (Position node) throws
  BoundaryViolationException, InvalidAccessorException;


  /**
   * @param child a node
   * @return rank of <code>child</code>
   *
   * @exception BoundaryViolationException if <code>child</code> is
   * the root
   * @exception InvalidAccessorException if <code>child</code> is null
   * or does not belong to this tree
   */
  public int rankOfChild (Position child) throws
  BoundaryViolationException, InvalidAccessorException;

  
}
