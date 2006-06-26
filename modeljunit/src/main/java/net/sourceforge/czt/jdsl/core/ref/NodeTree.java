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
 * A node-based Tree.  The Positions of the tree are
 * the nodes. <p>
 *
 * cut(), link(), and replaceSubtree() are implemented with 
 * O(n) running times
 * to support size() and contains() having O(1) running times.
 * Rank related methods 
 * are O(the maximum number of children per node). The tree is implemented
 * with a internal node data structure which keeps track
 * of the structure of the tree (i.e. links to parents, siblings,
 * and children).
 *
 * @author Galina Shubina (gs)
 * @version JDSL 2.1.1 
 */

public class NodeTree 
  extends AbstractPositionalContainer
  implements Tree {

    /**
     * The stored size of the Tree (never less then one)
     */
    private int size_;

    /**
     * The root node of the Tree
     */
    private NTNode root_;

    /**
     * Cache for positions
     */
    private NTNode[] poscache_;
    

    /**
     * Cache for elements
     */
    private Object[] eltcache_;


  // netsed class(es)
  
    /**
     * Internal tree node. This is a Position that takes care of all
     * children, sibling, and parent linkage.
     */
    private static class NTNode extends HashtableDecorable 
      implements Position {
	
	/**
	 * The parent of this node. It is null only when the tree is a root
	 * or it is uncontained.
	 */
	private NTNode parent_;

	/**
	 * The left sibling of this node in the tree. It is null 
	 * when the node does not have a left sibling or when it is uncontained.
	 */
	private NTNode left_; 

	/**
	 * The right sibling of this node in the tree. It is null when
	 * the node does not have a right sibling or when it is uncontained.
	 */
	private NTNode right_;

	/**
	 * The first child of this node. It does not have any left siblings.
	 * first_ is null if this node does not have any children.
	 */
	private NTNode first_; 

	/**
	 * The last child of this node. It does not have any right siblings.
	 * last_ is null if this node does not have any children.
	 */
	private NTNode last_; 

	/**
	 * The tree containing this node. This value is null if the node
	 * is uncontained.
	 */
	private InspectableContainer container_;

	/**
	 * The number of children this node has. It is zero when
	 * the node is an external node or when it is uncontained.
	 */
	private int num_children_;

	/**
	 * This node's element. May be null.
	 */
	private Object element_;
	
	/**
	 * This node's cache for its children's positions in order.
	 */
	private NTNode[] children_;

	/**
	 * Creates a new external node. 
	 * <p>
	 * O(1) time
	 * @param element element to be at this position
	 * @param c container in which this node is going to be
	 */
	private NTNode(Object element, InspectableContainer c) {
	  super();
	  element_ = element;
	  makeUncontained();
	  container_ = c;
	  num_children_ = 0;
	  children_ = null;
	}

	/**
	 * O(1) time
	 * @return the element stored at this position
	 */
	public Object element() { 
	  return element_; 
	}
	
	public String toString(){
	  return ToString.stringfor((Position)this);
	}

	/**
	 * O(1) time
	 * <p>
	 * Sets this node's parent.
	 */
	void setParent(NTNode parent) { 
	  parent_ = parent;
	}

	/**
	 * O(1) time
	 **/
	void addNumberOfChildren(int n) {
	  assert n>=0;
	  num_children_ += n;
	  if (n != 0)
	    children_ = null;
	}
	
	/**
	 * O(1) time
	 */
	void removeNumberOfChildren(int n) {
	  assert n>=0;
	  num_children_ -= n;
	  if (n != 0)
	    children_ = null;
	}
	

	/**
	 * O(1) time
	 * <p>
	 * Sets this node's left sibling.
	 */
	void setLeftSib(NTNode left) { 
	  left_ = left; 
	}
	
	/**
	 * O(1) time
	 * <p>
	 * Sets this node's right sibling.
	 */
	void setRightSib(NTNode right) { 
	  right_ = right; 
	}

	/**
	 * O(1) time
	 * <p>
	 * Sets this node's first child and invalidate the children cache.
	 */
	void setFirstChild(NTNode first) { 
	  first_ = first; children_ = null;
	}

	/**
	 * O(1) time
	 * <p>
	 * Sets this node's last child and invalidate the children cache.
	 */
	void setLastChild(NTNode last) { 
	  last_ = last; children_ = null;
	}

	/**
	 * O(1) time
	 * <p>
	 * Sets this node's container.
	 */
	void setContainer(InspectableContainer c) { 
	  container_ = c; 
	}
	
	/**
	 * O(1) time
	 * <p>
	 * Sets this node's element.
	 */
	void setElement(Object elt) { 
	  element_ = elt; 
	}

	/**
	 * O(1) time if children cache exists, 
	 * O(the number of children of this node) otherwise.
	 * @return PositionIterator iterator over the children nodes
	 */
	PositionIterator childrenIterator() {
	  int i;
	  NTNode tmp;
	  if (first_ == null)
	    return new ArrayPositionIterator(null);
	  if (children_ == null) {
	    children_ = new NTNode[num_children_];
	    for(i = 0, tmp = first_; i < num_children_; 
		i++, tmp = tmp.rightSib()) {
	      children_[i] = tmp;
	    }
	  } 
	  return new ArrayPositionIterator(children_);
	}

	/**
	 * O(1) time
	 */
	NTNode parent() { return parent_; }

	/**
	 * O(1) time
	 */
	NTNode leftSib() { return left_; }

	/**
	 * O(1) time
	 */
	NTNode rightSib() { return right_; }

	/**
	 * O(1) time
	 */
	NTNode firstChild() { return first_; }

	/**
	 * O(1) time
	 */
	NTNode lastChild() { return last_; }

	/**
	 * O(1) time
	 */
	int numChildren() { return num_children_; }

	/**
	 * O(1) time
	 */
	InspectableContainer container() { return container_; }

	/**
	 * Clears all fields of the node before making it uncontained.
	 * To make it completely uncontained one still has to update
	 * its parent, children, and left and right siblings to stop
	 * pointing to it.
	 * <p>
	 * O(1) time
	 */
	void makeUncontained() {
	  parent_ = null;
	  left_ = null;
	  right_ = null;
	  first_ = null;
	  last_ = null;
	  container_ = null;
	  num_children_ = 0;
	  children_ = null;
	}

	/**
	 * O(1) time
	 * 
	 * @return <i>true</i> if this node is external
	 */
	boolean isExternal() {
	  return (first_ == null);
	}
	
	/**
	 * O(the number of children of the node) time
	 * <p>
	 * Computes the rank of a child of this node.
	 * @param node child of this node
	 * @return rank of node with respect to its parent (this node)
	 */
	int rankOfChild(NTNode node) {
	  int rank = 0;
	  NTNode tmp = first_;
	  for( ; tmp != node; tmp = tmp.rightSib())
	    rank++;
	  return rank;
	}

	/**
	 * O(1)
	 *
	 * Inserts a sequence of nodes into this parents children list.
	 * <p>
	 * This method does the following things:
	 * <ul>
	 * <li> Removes nodes from <code>newLeft</code> to <code>newRight</code>
	 * (inclusive) from they old parent's children list
	 * <li> Removes nodes from <code>sibLeft</code> to <code>sibRight</code> (non inclusive)
	 * from this node's children list (<code>sibLeft</code> and <code>sibRight</code>
	 * must be its children)
	 * <li> Attaches the former children of this node to a new node <code>oldParent</code>
	 * <li> Attaches the nodes from <code>newLeft</code> to <code>newRight</code>
	 * (inclusive) to this node's children list between <code>sibLeft</code> and <code>sibRight</code>
	 * </ul>
	 *
	 * @param sibLeft sibling right of which to insert newLeft
	 * @param sibRight sibling left of which to insert newRight
	 * @param newLeft 
	 * @param newRight
	 * @param newParent becomes parent of whatever used to be between 
	 * <code>sibLeft</code> and <code>sibRight</code>, it can be either
	 * a null or a node with no children
	 * 
	 */
	void replace(NTNode sibLeft, NTNode sibRight, NTNode newLeft, NTNode newRight, NTNode newParent) {
	  int cnt_cut; // The number of nodes being cut from between sibLeft and sibRight
	  int cnt_inserted; // The number of nodes being inserted (i.e. from newLeft to newRight inclusive)
	  NTNode tmp;
	  NTNode oldLeft; // The leftmost child to be cut, if any (i.e. the right sibling of sibLeft)
	  NTNode oldRight; // The rightmost child to be cut, if any (i.e. the left sibling of sibRight)

	  oldLeft = ( sibLeft == null ? first_ : sibLeft.rightSib() );
	  oldRight = ( sibRight == null ? last_ : sibRight.leftSib() );

	  // Remove children between sibLeft and sibRight from this node
	  if (oldLeft == sibRight) {
	    assert oldRight == sibLeft;
	    cnt_cut = 0;
	  } else {
	    for(cnt_cut = 0, tmp = oldLeft; tmp != sibRight && tmp != null; 
		tmp = tmp.rightSib(), cnt_cut++) {
	      tmp.setParent(newParent);
	    }
	    if (oldLeft != null) oldLeft.setLeftSib(null);
	    if (oldRight != null) oldRight.setRightSib(null);
	    if (newParent != null) {
	      newParent.addNumberOfChildren(cnt_cut);
	      assert newParent.firstChild() == null;
	      newParent.setFirstChild(oldLeft);
	      newParent.setLastChild(oldRight);
	    }
	    removeNumberOfChildren(cnt_cut);
	  }

	  if (newLeft == null) { 
	    // Nothing to be inserted - just connect sibLeft and sibRight
	    assert newRight == null;
	    cnt_inserted = 0;
	    if (sibLeft == null) first_ = sibRight;
	    else sibLeft.setRightSib(sibRight);
	    if (sibRight == null) last_ = sibLeft;
	    else sibRight.setLeftSib(sibLeft);
	  } else {
	    // Make the nodes to be inserted part of the tree
	    assert newLeft != null && newRight != null;
	    NTNode oldParent = newLeft.parent();
	    for(cnt_inserted = 1, tmp = newLeft; tmp != null; 
		cnt_inserted++, tmp = tmp.rightSib()) {
	      tmp.setParent(this);
	      if (tmp == newRight) break;
	    }
	    assert tmp != null;
	    if (oldParent != null) {
	      // Adjust the old parent of the nodes between newLeft and newRight
	      // to not point or count these nodes anymore
	      oldParent.removeNumberOfChildren(cnt_inserted);
	      if (oldParent.firstChild() == newLeft)
		oldParent.setFirstChild(newRight.rightSib());
	      if (oldParent.lastChild() == newRight)
		oldParent.setLastChild(newLeft.leftSib());
	    }
	    // Adjust old siblings of newLeft and newRight to not
	    // point to them anymore
	    if (newLeft.leftSib() != null)
	      newLeft.leftSib().setRightSib(newRight.rightSib());
	    if (newRight.rightSib() != null)
	      newRight.rightSib().setLeftSib(newLeft.leftSib());
	    // Do the actual linking of these nodes to this node
	    // and this node's list of children
	    addNumberOfChildren(cnt_inserted);
	    if (sibLeft == null) first_ = newLeft;
	    else sibLeft.setRightSib(newLeft);
	    if (sibRight == null) last_ = newRight;
	    else sibRight.setLeftSib(newRight);
	    newLeft.setLeftSib(sibLeft);
	    newRight.setRightSib(sibRight);
	  }
	}
    }

    //////////////////////////////////////////////////////////////////
    // Constructors
    //////////////////////////////////////////////////////////////////

    /**
     * The default constructor for NodeTree, which creates a tree
     * with one node whose element is null. This is the only public
     * constructor.
     */
    public NodeTree() {
      size_ = 1;
      root_ = new NTNode(null, this);
      poscache_ = null;
      eltcache_ = null;
    }
    
    /**
     * Constructor to be used to create new trees in cut and
     * replaceSubtree methods which require part of the tree
     * to be returned as a new tree.
     */
    private NodeTree(NTNode root) {
      root.setParent(null);
      root.setLeftSib(null);
      root.setRightSib(null);
      root_ = root;
      size_ = updateContainer(root_,this);
      poscache_ = null;
      eltcache_ = null;
    }

    //////////////////////////////////////////////////////////////////
    // Methods implemented from InspectableContainer
    //////////////////////////////////////////////////////////////////

    /**
     * O(1) time
     */
    public boolean contains(Accessor a) 
      throws InvalidAccessorException  {
	if (a == null)
	  throw new InvalidAccessorException("A null position cannot be contained.");
	if (! (a instanceof NTNode))
	  return false;            
	if (((NTNode)a).container() == this) 
	  return true;
	else
	  return false;
    }

    /**
     * O(1) time
     */
    public boolean isEmpty() {
      return false;
    }

    /**
     * O(1) time
     */
    public int size() {
      return size_;
    }


    /**
     * O(1) time if cache already exists, O(size of the tree) otherwise
     */
    public ObjectIterator elements() {
      if (eltcache_ == null) {
	int i = 0;
	eltcache_ = new Object[size_];
	PositionIterator posIter = positions();
	while(posIter.hasNext()) {
	  eltcache_[i] = posIter.nextPosition().element();
	  i++;
	}
      }
      return new ArrayObjectIterator(eltcache_);
    }

    //////////////////////////////////////////////////////////////////
    // Methods implemented from Container
    //////////////////////////////////////////////////////////////////

    /**
     * O(1) time
     */
    public Container newContainer() {
      return new NodeTree();
    }

    /**
     * O(1) time
     */
    public Object replaceElement(Accessor a, Object newElement) 
      throws InvalidAccessorException {
	NTNode node = checkValid(a);
	// Clear the elements but not the psoition cache
	eltcache_ = null;
	Object old = node.element();
	node.setElement(newElement);
	return old;
    }

    //////////////////////////////////////////////////////////////////
    // Methods implemented from InspectablePositionalContainer
    //////////////////////////////////////////////////////////////////

    /**
     * O(1) time if cache already exists, O(size of the tree) otherwise
     */
    public PositionIterator positions() {
	if (poscache_ == null) {
	  int fromNode, toNode;
	  NTNode tmp;
	  poscache_ = new NTNode[size_];
	  poscache_[0] = root_;
	  for(fromNode = 0, toNode = 1; fromNode < size_; fromNode++) {
	    if (poscache_[fromNode].isExternal())
	      continue;
	    for(tmp = poscache_[fromNode].firstChild(); tmp != null; tmp = tmp.rightSib()) {
	      poscache_[toNode] = tmp;
	      toNode++;
	    }
	  }
	}
	return new ArrayPositionIterator(poscache_);
    }

    //////////////////////////////////////////////////////////////////
    // Methods implemented from PositionalContainer
    //////////////////////////////////////////////////////////////////
    /**
     * O(1) time
     */
    public void swapElements(Position a, Position b) 
      throws InvalidAccessorException {
	NTNode nodea = checkValid(a);
	NTNode nodeb = checkValid(b);
	Object obja = nodea.element();
	nodea.setElement(nodeb.element());
	nodeb.setElement(obja);
    }

    //////////////////////////////////////////////////////////////////
    // Methods implemented from InspectableTree 
    //////////////////////////////////////////////////////////////////

    /**
     * O(1) time
     */
    public boolean isRoot(Position node)
      throws InvalidAccessorException {
	NTNode tnode = checkValid(node);
	return (tnode == root_);
    }

    /**
     * O(1) time
     */
    public boolean isInternal(Position node)
      throws InvalidAccessorException {
	NTNode tnode = checkValid(node);
	return (!tnode.isExternal());
    }
    
    /**
     * O(1) time
     */
    public boolean isExternal(Position node)
      throws InvalidAccessorException {
	NTNode tnode = checkValid(node);
	return tnode.isExternal();
    }

    /**
     * O(1) time
     */
    public Position root() {
	return root_;
    }

    /**
     * O(1) time
     */
    public Position parent(Position node) 
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(node);
	if (tnode == root_)
	  throw new BoundaryViolationException("Root of a tree cannot have a parent.");
	return tnode.parent();
    }


    /**
     * O(1) time if cache exists,
     * O(the number of children of the node) otherwise.
     */
    public PositionIterator children(Position node) 
      throws InvalidAccessorException {
	NTNode tnode = checkValid(node);
	return tnode.childrenIterator();
    }

    /**
     * O(the number of children of the node) time
     */
    public PositionIterator siblings(Position node) 
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(node), tmp;
	if (tnode == root_)
	  throw new BoundaryViolationException("Root of a tree cannot have any siblings.");
	int numsib = tnode.parent().numChildren()-1, i;
	if (numsib == 0)
	  return new ArrayPositionIterator(null);
	NTNode [] siblings = new NTNode[numsib];
	for(tmp = tnode.parent().firstChild(), i = 0; i < numsib; i++, tmp = tmp.rightSib()) {
	  if (tmp == tnode)
	    i--;
	  else
	    siblings[i] = tmp;
	}
	return new ArrayPositionIterator(siblings);
    }

    /**
     * O(1) time
     */
    public int numChildren(Position node)
      throws InvalidAccessorException {
	NTNode tnode = checkValid(node);
	return tnode.numChildren();
    }

    /**
     * O(1) time
     */
    public Position siblingAfter(Position node)
      throws BoundaryViolationException, InvalidAccessorException {
	 NTNode tnode = checkValid(node);
	 if (tnode == root_)
	   throw new BoundaryViolationException("Root of a tree cannot have any siblings.");
	 NTNode right = tnode.rightSib();
	 if (right == null)
	   throw new BoundaryViolationException("Position is the last child.");
	 return right;
    }

    /**
     * O(1) time
     */
    public Position childAtRank(Position node, int rank)
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(node);
	if (rank < 0 || rank >= tnode.numChildren())
	  throw new BoundaryViolationException("Invalid rank of a child.");
	NTNode tmp = tnode.firstChild();
	for(int i=0; i<rank; i++, tmp = tmp.rightSib());
	return tmp;
    }

    /**
     * O(the number of children of the node) time
     */
    public Position siblingBefore(Position node)
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(node);
	if (tnode == root_)
	  throw new BoundaryViolationException("Root of a tree cannot have any siblings.");
	NTNode left = tnode.leftSib();
	if (left == null)
	  throw new BoundaryViolationException("Position is the first child.");
	return left;
    }

    /**
     * O(1) time
     */
    public Position firstChild(Position node)
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(node);
	if (tnode.isExternal())
	  throw new BoundaryViolationException("Position is external.");
	return tnode.firstChild();
    }

    /**
     * O(1) time
     */
    public Position lastChild(Position node)      
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(node);
	if (tnode.isExternal())
	  throw new BoundaryViolationException("Position is external.");
	return tnode.lastChild();
    }

    /**
     * O(the number of children of the node) time
     */
    public int rankOfChild(Position child) 
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tnode = checkValid(child);
	if (tnode == root_)
	  throw new BoundaryViolationException("Position is a root.");

	return tnode.parent().rankOfChild(tnode);
    }

    //////////////////////////////////////////////////////////////////
    // Methods implemented from Tree interface
    //////////////////////////////////////////////////////////////////
    //              On the issue of cut and link:
    // cut does not build on replaceSubtree, because it does not need
    // any container checks as well as creation of new objects (other then
    // the return tree) to make it work. Same is true for link: while
    // checks are not an issue here, not using replaceSubtree let's us 
    // avoid creation and update of the return subtree.
    //////////////////////////////////////////////////////////////////
    /**
     * O(size of the cut subtree) time
     */
    public Tree cut(Position p) 
      throws InvalidAccessorException {
	NTNode tnode = checkValid(p);
	NTNode new_node = new NTNode(null, this);
	NTNode parent = tnode.parent();
	if (parent == null) {
	  root_ = new_node;
	} else {
	  parent.replace(tnode.leftSib(), tnode.rightSib(), new_node, new_node, null);
	}
	poscache_ = null;
	eltcache_ = null;
	
	NodeTree new_tree =  new NodeTree(tnode);
	size_ -= new_tree.size()-1;
	return new_tree;
    }

    /**
     * O(size of the new subtree to be linked in) time
     */
    public Object link(Position extNode, Tree t) 
      throws InvalidAccessorException, InvalidContainerException {
	NTNode tnode = checkValid(extNode);
	if (! tnode.isExternal()) 
	  throw new InvalidAccessorException("A tree cannot be linked to an internal node.");
	if (t == null)
	  throw new InvalidContainerException("A null tree cannot be linked.");
	if (! (t instanceof NodeTree))
	  throw new InvalidContainerException("Incompatible type of a tree"); 
	if (t == this)
	  throw new InvalidContainerException("A tree cannot be linked to itself.");
	NTNode subtree_root = (NTNode)t.root();
	int subtree_size = updateContainer(subtree_root, this);

	NTNode parent = tnode.parent();
	poscache_ = null;
	eltcache_ = null;
	((NodeTree)t)._clear();

	if (parent != null)
	  parent.replace(tnode.leftSib(), tnode.rightSib(), subtree_root, subtree_root, null);
	else
	  root_ = subtree_root;
	tnode.makeUncontained();
	size_ += subtree_size-1;
	return tnode.element();
    }

    /**
     * O(size of the new subtree + size of the cut tree) time
     */
    public Tree replaceSubtree(Position node, Tree t)
      throws InvalidAccessorException, InvalidContainerException {
	NTNode old_root = checkValid(node);
	if (t == null)
	  throw new InvalidContainerException("A null tree cannot be linked.");
	NTNode new_root = (NTNode)t.root();
	if (! (t instanceof NodeTree))
	  throw new InvalidContainerException("Incompatible type of tree");
	NodeTree new_tree = (NodeTree)t;
	if (new_tree == this)
	  throw new InvalidContainerException("A tree cannot be linked to itself.");
	int new_size, old_size;
	new_size = new_tree.size();
	new_tree._clear();
	updateContainer(new_root, this);
	NTNode parent = old_root.parent();	
	if (parent == null) {
	  root_ = new_root;
	} else {
	  parent.replace(old_root.leftSib(), old_root.rightSib(), new_root, new_root, null);
	}
	poscache_ = null;
	eltcache_ = null;

	NodeTree to_return = new NodeTree(old_root);
	size_ = size_ - to_return.size() + new_size;
	return to_return;
    }

    /**
     * O(1) time
     */
    public Position insertAfterSibling(Position node, Object elem) 
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tbefore = checkValid(node);
	if (node == root_)
	  throw new BoundaryViolationException("Root cannot have any siblings.");
	poscache_ = null;
	eltcache_ = null;
	size_++;

	NTNode new_node = new NTNode(elem, this);
	tbefore.parent().replace(tbefore, tbefore.rightSib(), new_node, new_node, null);

	return new_node;
    }

    /**
     * O(the number of children of the node) time
     */
    public Position insertChildAtRank(Position node, int rank, Object elem)
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode parent = checkValid(node);
	NTNode tmp;
	if (rank < 0)
	  throw new BoundaryViolationException("A child cannot have negative rank.");
	if (rank == 0) {
	  tmp = null;
	} else {
	  tmp = parent.firstChild();
	  for(int i=0; i < rank-1 && tmp != null; i++, tmp = tmp.rightSib());
	  if (tmp == null)
	    throw new BoundaryViolationException("Rank is greater then the number of children.");
	}
	poscache_ = null;
	eltcache_ = null;
	size_++;

	NTNode new_node = new NTNode(elem, this);
	parent.replace(tmp, (tmp == null ? parent.firstChild() : tmp.rightSib()), 
		       new_node, new_node, null);

	return new_node;
    }

    /**
     * O(1) time
     */
    public Position insertBeforeSibling(Position node, Object elem) 
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode tafter = checkValid(node);
	if (node == root_)
	  throw new BoundaryViolationException("Root cannot have any siblings.");
	NTNode parent = tafter.parent();
	poscache_ = null;
	eltcache_ = null;
	size_++;

	NTNode new_node = new NTNode(elem, this);
	parent.replace(tafter.leftSib(), tafter, new_node, new_node, null);

	return new_node;
    }

    /**
     * O(1) time
     */
    public Position insertFirstChild(Position node, Object elem)
      throws InvalidAccessorException {
	NTNode parent = checkValid(node);
	poscache_ = null;
	eltcache_ = null;
	size_++;	

	NTNode new_node = new NTNode(elem, this);
	parent.replace(null, parent.firstChild(), new_node, new_node, null);
	
	return new_node;
    }

    /**
     * O(1) time
     */
    public Position insertLastChild(Position node, Object elem)
      throws InvalidAccessorException {
	NTNode parent = checkValid(node);
	poscache_ = null;
	eltcache_ = null;
	size_++;

	NTNode new_node = new NTNode(elem, this);
	parent.replace(parent.lastChild(), null, new_node, new_node, null);

	return new_node;
    }

    /**
     * O(1) time
     */
    public Object removeExternal(Position node) 
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode to_remove = checkValid(node);
	if (! to_remove.isExternal()) 
	  throw new BoundaryViolationException("Position is internal.");
	if (to_remove == root_)
	  throw new BoundaryViolationException("Root of a tree cannot be removed.");
	poscache_ = null;
	eltcache_ = null;
	size_--;
	to_remove.parent().replace(to_remove.leftSib(), to_remove.rightSib(), null, null, null);
	to_remove.makeUncontained();
	return to_remove.element();
    }

    /**
     * O(1) time
     */
    public Object contract(Position node)
      throws BoundaryViolationException, InvalidAccessorException {
	NTNode to_remove = checkValid(node);
	if (to_remove == root_)
	  throw new BoundaryViolationException("Root of a tree cannot be contracted.");
	if (to_remove.isExternal())
	  throw new BoundaryViolationException("Cannot contract external node.");

	poscache_ = null;
	eltcache_ = null;
	size_--;
	to_remove.parent().replace(to_remove.leftSib(), to_remove.rightSib(), to_remove.firstChild(),
				   to_remove.lastChild(), null);
	to_remove.makeUncontained();
	return to_remove.element();
    }

    /**
     * O(number of children of a new node) time
     */
    public Position expand(Position fromChild, Position toChild, Object elem) 
      throws InvalidAccessorException {
	NTNode tfrom = checkValid(fromChild);
	NTNode tto = checkValid(toChild), tmp;
	for(tmp = tfrom; (tmp != null) && (tmp != tto); tmp = tmp.rightSib());
	if (tmp == null)
	  throw new InvalidAccessorException("Cannot expand the tree where the second position is not a higher order sibling of the first.");
	poscache_ = null;
	eltcache_ = null;
	size_++;
	
	NTNode newnode = new NTNode(elem, this);
	NTNode oldparent = tfrom.parent();
	if (oldparent != null)
	  oldparent.replace(tfrom.leftSib(), tto.rightSib(), newnode, newnode, newnode);
	else {
	  root_ = newnode;
	  newnode.replace(null, null, tfrom, tto, null);
	}
	return newnode;
    }

    /**
     * Checks whether the accessor is valid and belongs to this container.
     * O(1) assuming container check is O(1).
     * 
     * @param p accessor to be checked out
     * @exception InvalidAccessorException if the accessor is null,
     * or if it is of the wrong class, or it doesn't belong to this container.
     * @return NTNode cast down Position of this container
     */
    private NTNode checkValid(Accessor p)
      throws InvalidAccessorException {
	if (p == null)
	  throw new InvalidAccessorException("A null position cannot be contained.");
	if (! (p instanceof NTNode))
	  throw new InvalidAccessorException("Position of wrong class: " +
					     p.getClass());
	if (((NTNode)p).container() != this) 
	  throw new InvalidAccessorException("Position does not belong to the container.");

	return (NTNode)p;
    }

    /**
     * Updates container variable in the entire subtree rooted at a node. Implemented
     * using basic depth first search down the subtree.
     * @return int size of the tree rooted at node
     */
    private int updateContainer(NTNode node, InspectableContainer c) {
      int size = 0;
      NTNode proc_node;
      for(proc_node = node; proc_node != null;) {
	proc_node.setContainer(c);
	size++;
	if (proc_node.isExternal()) {
	  // backtrack up until find a node with a right sibling or get back to the node.
	  for(; (proc_node != node) && (proc_node.rightSib() == null); proc_node = proc_node.parent());
	  if (proc_node == node)
	    break;
	  proc_node = proc_node.rightSib();
	} else {
	  proc_node = proc_node.firstChild();
	}
      }
      return size;
    }

    /**
     * Clears the tree to a pristine condition of having one empty node.
     */
    private void _clear() {
      size_ = 1;
      root_ = new NTNode(null, this);
      poscache_ = null;
      eltcache_ = null;
    }

    public String toString() {
      return ToString.stringfor(this);
    }

}
