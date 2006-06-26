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
 * A modifiable tree in which each node has
 * either zero or two children.
 *
 * Binary trees are conceived as starting with a single external node
 * (a/k/a leaf) at the root.  (The node's initial element is null.)
 * Thus, a BinaryTree is never empty (isEmpty() is always false).
 * Furthermore, since size() returns the number of internal and
 * external leaves, size() is always at least 1.
 *
 * The splicing methods, link(.) and replaceSubtree(.), leave the
 * spliced-in container with a single external node storing null.
 *
 * The iterator() of a BinaryTree gives nodes in preorder.
 *
 * Note that a (modifiable) BinaryTree cannot be used where a (modifiable)
 * <i>Tree</i> is needed (it would violate the Liskov Substitution
 * Principle, because a tree has the ability to insert arbitrary numbers of children).
 * Hence this interface does not extend the
 * <code>Tree</code> interface. For the inspectable counterparts the
 * substitution principle holds, so <i>InspectableBinaryTree</i> is a
 * subinterface of <i>InspectableTree</i>.
 *
 * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Mike Boilen (mgb)
 * @author Andrew Schwerin (schwerin)
 * @see InspectableBinaryTree
 */
public interface BinaryTree extends InspectableBinaryTree,
				    PositionalContainer {


  /** 
   * The external position specified is transformed into an internal,
   * and it gains two external children.  The position reference
   * itself doesn't change.  The elements of its two new, external
   * children are both null.
   * 
   * @param node any external position in this binary tree
   *
   * @exception InvalidAccessorException if <code>node</code> is not
   * external, is null, or does not belong to this binary tree.
   */
  public void expandExternal (Position node) throws InvalidAccessorException;

  
  /** 
   * The parent of <code>node</code> is deleted, and the sibling of
   * <code>node</code>, with all its children, is installed in its
   * place; <code>node</code> is also deleted.
   *
   * @param node any external position in this binary tree
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * an external position, as required, but also the root of this binary
   * tree.
   * @exception InvalidAccessorException if <code>node</code> is not
   * external, is null, or does not belong to this binary tree.
   */
  public void removeAboveExternal (Position node)
    throws BoundaryViolationException, InvalidAccessorException;


  /** 
   * Position </code>node</code> and all its children are removed from
   * this binary tree and replaced with a new external node with a
   * null element.  They are packaged in a new binary tree and
   * returned; all positions elements are still valid, although some
   * of them have a different container after the operation.
   * </code>node</code> can be the root, or an external node.
   *
   * @param node the position above which to make the cut
   * @return the subtree removed, packaged as a new BinaryTree, with
   * <code>node</code> as its root
   *
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this binary tree.
   */
  public BinaryTree cut (Position node) throws InvalidAccessorException;


  /** 
   * Links binary tree <code>newSubtree</code> at external node
   * <code>node</code> by replacing <code>node</code> with the root of
   * <code>newSubtree</code>.  As a result of this method, the
   * positions of <code>newSubtree</code> become positions of this
   * binary tree and <code>newSubtree</code> becomes a binary tree
   * with a single node storing null.
   * 
   * @param node the external node to replace with the new subtree
   * @param newSubtree the subtree to link in
   *
   * @return the element of the external position that was removed
   *
   * @exception InvalidAccessorException if <code>node</code> is not
   * external, is null, or does not belong to this binary tree.
   * @exception InvalidContainerException if <code>newSubtree</code>
   * is null, incompatible with, or equal to this binary tree.
   */
  public Object link (Position node, BinaryTree newSubtree)
    throws InvalidAccessorException, InvalidContainerException;
  

  /**
   * Swaps a subtree of this binary tree with a binary tree passed in.
   * In the extremes, the subtree of this binary tree might be the
   * entire tree, or might be just a leaf.  <code>subtreeRoot</code>
   * specifies a subtree of this binary tree.  That subtree is removed
   * from this binary tree, and <code>newSubtree</code> is linked in in
   * its place.  A new binary tree, whose root is the position
   * <code>subtreeRoot</code>, is returned to the user (this binary
   * tree has all the positions of the removed subtree).
   *
   * Note that this binary tree is one of three binary trees involved
   * in the method.  The other two are the newSubtree passed in, which
   * becomes an empty tree when the method finishes; and the tree
   * returned, which is a brand new BinaryTree holding the
   * subtreeRoot, and all its children, which were removed from this
   * binary tree.
   * 
   * Note that <code>link(.)</code> and <code>cut(.)</code> can both
   * be implemented in terms of this method.
   *
   * <code>newSubtree</code> must be of the same class as this binary
   * tree, or perhaps otherwise node-compatible with this binary tree.
   * 
   * @param subtreeRoot any position in this binary tree
   * @param newSubtree the binary tree that will replace the binary
   * tree rooted at <code>subtreeRoot</code>
   * @return a new binary tree, with <code>subtreeRoot</code> as its
   * root
   *
   * @exception InvalidAccessorException if <code>subtreeRoot</code>
   * is null or does not belong to this binary tree.
   * @exception InvalidContainerException if <code>newSubtree</code>
   * is null, incompatible with, or equal to this binary tree.
   */
  public BinaryTree replaceSubtree (Position subtreeRoot,
				    BinaryTree newSubtree)
    throws InvalidAccessorException, InvalidContainerException;


  /**
   * Position <code>subtreeRoot</code> of this binary tree is demoted
   * one level, with all the positions and elements unchanged, and
   * becomes the right child of a new node storing the given element.
   * The root of <code>newSubtree</code>, with all its children, is
   * linked in as the left child of the new node, with all the
   * positions and elements unchanged.  newSubtree becomes empty.
   *
   * @param newSubtree the binary tree whose root will be linked in as
   * the left child of the new node
   * @param eltOfParent the object to be stored in the new node
   * @param subtreeRoot any position in this binary tree
   *
   * @exception InvalidAccessorException if <code>subtreeRoot</code>
   * is null or does not belong to this binary tree.
   * @exception InvalidContainerException if <code>newSubtree</code>
   * is null, incompatible with, or equal to this binary tree.
   */
  public void graftOnLeft (Position subtreeRoot, Object eltOfParent,
			    BinaryTree newSubtree)
    throws InvalidAccessorException, InvalidContainerException;


  /**
   * Position <code>subtreeRoot</code> of this binary tree is demoted
   * one level, with all the positions and elements unchanged, and
   * becomes the left child of a new node, storing the given element.
   * The root of <code>newSubtree</code>, with all its children, is
   * linked in as the right child of the new node, with all the
   * positions and elements unchanged.  newSubtree becomes empty.
   *
   * @param subtreeRoot any position in this binary tree
   * @param eltOfParent the object to be stored in the new node
   * @param newSubtree the binary tree whose root will be linked in as
   * the right child of the new node
   *
   * @exception InvalidAccessorException if <code>subtreeRoot</code>
   * is null or does not belong to this binary tree.
   * @exception InvalidContainerException if <code>newSubtree</code>
   * is null, incompatible with, or equal to this binary tree.
   */
  public void graftOnRight (Position subtreeRoot, Object eltOfParent,
			    BinaryTree newSubtree)
    throws InvalidAccessorException, InvalidContainerException;


}
