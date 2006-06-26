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
  * Please refer to the documentation of the <code>BinaryTree</code> interface.
  *
  * @version JDSL 2.1.1 
 * @author Mike Boilen (mgb)
  * @see BinaryTree
  */
public interface InspectableBinaryTree extends InspectableTree {
    
    
  /** 
   * Provides the left child of a given node.
   * 
   * @param node Any internal node of the tree
   * @return left child of <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * external
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this binary tree.
   */
  public Position leftChild (Position node)
    throws BoundaryViolationException, InvalidAccessorException;


  /**
   * Provides the right child of a given node.
   * 
   * @param node Any internal node of the tree
   * @return right child of <code>node</code>
   *
   * @exception BoundaryViolationException if <code>node</code> is
   * external
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this binary tree.
   */
  public Position rightChild (Position node)
    throws BoundaryViolationException, InvalidAccessorException;
  

  /**
   * Provides the sibling of a given node (the other child of the
   * node's parent)
   * 
   * @param node a node of the binary tree.
   * @return sibling of <code>node</code>.
   *
   * @exception BoundaryViolationException if <code>node</code> is the
   * root
   * @exception InvalidAccessorException if <code>node</code> is null
   * or does not belong to this binary tree.
   */
  public Position sibling (Position node)
    throws InvalidAccessorException, BoundaryViolationException;
  
}
