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
 * A positional container representing an ordered tree.
 * The children of each internal node
 * are ordered. A tree always has at least one node
 * (<code>isEmpty()</code> always returns <code>false</code>). The
 * smallest tree is a single external node.
 *
 * @author Mark Handy
 * @author Mike Boilen (mgb)
 * @author Andrew Schwerin (schwerin)
 * @author Luca Vismara (lv)
 * @author Galina Shubina (gs)
 * @version JDSL 2.1.1 
 * @see InspectableTree
 */
public interface Tree extends InspectableTree, PositionalContainer {

  // update methods
  
  /**
   * Cuts this tree above the given <code>node</code>, and replaces
   * this position with an external node with a null element. The
   * subtree cut off at that point is returned to the user as a brand
   * new <code>Tree</code> intstance.
   *
   * @param node The position above which to make the cut; 
   * will be the root of the returned tree
   * @return the subtree cut off of the tree.
   *
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree.
   */
  public Tree cut (Position node) throws InvalidAccessorException;


  /**
   * Links tree <code>t</code> at external node <code>extNode</code>
   * by replacing <code>ExtNode</code> with the root of <code>t</code>.
   * As a result of this method, the positions of tree <code>t</code>
   * become positions of this tree and tree <code>t</code> becomes
   * a tree with a single node with a null element.
   *
   * @param extNode The position to insert the tree
   * <code>t</code> at.
   * @param t The subtree to insert at the position.
   * @return The object contained in the eliminated
   * <code>extNode</code>
   *
   * @exception InvalidAccessorException if <code>extNode</code> is
   * not external, is null, or does not belong to this tree.
   *
   * @exception InvalidContainerException if <code>t</code> is null,
   * incompatible with, or equal to this tree.
   */
  public Object link (Position extNode, Tree t) throws
  InvalidAccessorException, InvalidContainerException ;

  
  /**
   * Replaces the subtree rooted at <code>node</code> with the tree
   * <code>t</code>.  The positions of <code>t</code> become positions
   * of this tree.  The cut subtree with the <code>node</code> as its
   * root is returned to the user as a new tree instance. All the
   * positions of this subtree become positions of this new tree.
   *
   * Note that <code>link(.)</code> and <code>cut(.)</code> can both
   * be implemented in terms of this method.
   *
   * @param node a node
   * @param t the tree that will replace the tree rooted
   * at <code>node</code>
   * @return A new tree, with <code>node</code> as its root
   *
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree.
   *
   * @exception InvalidContainerException if <code>t</code> is null,
   * incompatible with, or equal to this tree.
   */
  public Tree replaceSubtree (Position node, Tree t) throws
  InvalidAccessorException, InvalidContainerException;

  
  /**
   * Inserts a new sibling after a given node
   *
   * @param node a node different from the root
   * @param elem the object to be stored in the new node
   * @return the new node
   *
   * @exception BoundaryViolationException if <code>node</code> is the root
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position insertAfterSibling (Position node, Object elem) throws
  BoundaryViolationException, InvalidAccessorException;

  
  /**
   * Inserts a new child of node at the specified rank.
   *
   * @param node a node
   * @param rank an integer index of the children of node
   * from 0 to numChildren(node) (inclusive)
   * @param elem the object to be stored in the new node
   * @return the new node
   *
   * @exception BoundaryViolationException if <code>rank</code> < 0 or
   * <code>rank</code> > numChildren(<code>node</code>)
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position insertChildAtRank (Position node, int rank, Object elem)
    throws BoundaryViolationException, InvalidAccessorException;

  
  /**
   * Inserts a new sibling before a given node.
   *
   * @param node a node
   * @param elem the object to be stored in the new node
   * @return the new node
   *
   * @exception BoundaryViolationException if <code>node</code> is the root
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position insertBeforeSibling (Position node, Object elem) throws
  BoundaryViolationException, InvalidAccessorException;

  
  /**
   * Inserts a new child of <code>node</code> as the first child.
   *
   * @param node a node
   * @param elem the object to be stored in the new node
   * @return the new node
   *
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position insertFirstChild (Position node, Object elem) throws
  InvalidAccessorException;

  
  /**
   * Inserts a new child of node as the last child.
   *
   * @param node a node
   * @param elem the object to be stored in the new node
   * @return the new node
   *
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Position insertLastChild (Position node, Object elem) throws
  InvalidAccessorException;


  /**
   * Removes an external node (a leaf).
   *
   * @param node a leaf node different from the root
   * @return the object stored in <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is not
   * external or is the root
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Object removeExternal (Position node) throws
  BoundaryViolationException, InvalidAccessorException;

  
  /**
   * Replaces a node with its children in the appropriate order. It
   * removes <code>node</code>, and then inserts its children,
   * maintaining their order, between siblingBefore(<code>node</code>)
   * and siblingAfter(<code>node</code>).
   *
   * @param node a node
   * @return the object stored in <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is the
   * root or an external node
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this tree
   */
  public Object contract (Position node) throws BoundaryViolationException,
  InvalidAccessorException;

  
  /**
   * Replaces a set of consecutive children with a new node having
   * those children as its children in the appropriate order. It
   * removes the children between <code>fromChild</code> and
   * <code>toChild</code> (inclusive), inserts a new node in their
   * place, and makes the removed children the children of the new
   * node, maintaining their order.
   *
   * @param fromChild a node
   * @param toChild any higher-ranked sibling of 
   * <code>fromChild</code> or <code>fromChild</code> itself
   * @param elem the object to be stored in the new node
   * @return the new node
   *
   * @exception InvalidAccessorException if <code>fromChild</code> and
   * <code>toChild</code> are not siblings, or if <code>toChild</code>
   * is a lower-ranked sibling of <code>fromChild</code>, or if either
   * of them is null or does not belong to this tree
   */
  public Position expand (Position fromChild, Position toChild, Object elem)
    throws InvalidAccessorException;

}

