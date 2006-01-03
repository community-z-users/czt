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
 * A node-based Binary Tree. The Positions of the tree are
 * the nodes.<p>
 * 
 * contains() is O(1) time; so replaceSubtree, cut, and link are O(S), where S is the
 * number of positions in that subtree.
 * Positions() and elements() are O(N) -- where N is the number of positions
 * in the entire tree.
 * All other methods are O(1) time.
 * <p>
 * Elements can be stored at both internal and external (leaf) nodes.<p>
 *
 * The data structure stores a supernode which in turn stores the root.
 * (this supernode is invisible to the end user)
 *
 * You are only allowed to link in and replaceSubtree with other instances
 * of NodeBinaryTree (or subclasses thereof).
 *
 * @author Ryan Baker (rsb)
 * @author Mark Handy (mdh)
 * @author Benoit Hudson (bh)
 * @version JDSL 2.1.1 
 * @see AbstractPositionalContainer
 * @see BinaryTree
 */

public class NodeBinaryTree extends AbstractPositionalContainer 
implements BinaryTree {
    
  /**
    * The super node which stores the root.
    * (This should _never_ be null)
    */
    private NBTSuperNode _supernode;
    
  /**
    * The size of the tree
    * protected so that RestructurableNodeBinaryTree can access it
    */
  protected int _size;

   /** 
     * Create a tree.  The tree has a single external node
     * at its root, with element <code>null</code>.
     */
    public NodeBinaryTree() {
      _size = 1;
      _supernode = new NBTSuperNode (this, null);
      NBTNode root = new NBTNode (_supernode, (Object)null);
      _supernode.setRoot (root);
      root.setContainer(this);
    }
    
    /** 
     * Create a tree from a set of nodes.  The tree will
     * have as its root the given node.
     *
     * This constructor is protected in order to prevent it
     * from being used except as a result of operations on
     * one tree that create another tree
     *
     * It is assumed that the method calling this will take
     * responsibility for changing the container_ of the
     * various internal NBTNodes, as well as setting _size -- 
     * this way, we can allow
     * O(1) time access where appropriate
     * @param root Root of a tree of existing nodes.
     * @throws InvalidAccessorException when the given root has a parent.
     */
    protected NodeBinaryTree (NBTNode root)throws InvalidAccessorException {
      if (root.parent()!=null)	
	throw new InvalidAccessorException("Given root has a parent.");
        _supernode = new NBTSuperNode(this,root);
	root.setParent(_supernode);
	_size = 0;
    }
    


    /**
     *--------------------------------------------------------
     * From interface BinaryTree
     *--------------------------------------------------------
     */

  /**
    * Takes O(S) time, where S is the number of positions in the new
    * subtree to graft on
    * You are only allowed to link in and replaceSubtree with other instances
    * of NodeBinaryTree (or subclasses thereof)
    */
  public void graftOnLeft( Position subtree, Object eltOfParent, BinaryTree newSibling ){
    NBTNode NBTsubtree = checkPosition(subtree);

    NBTNode graftOnto = NBTsubtree.parent();
    NBTNode newSubtreeRoot = new NBTNode(graftOnto,eltOfParent);
    newSubtreeRoot.setContainer(this);

    if (graftOnto==_supernode)
      _supernode.setRoot(newSubtreeRoot);
    else
      graftOnto.setChild(NBTsubtree,newSubtreeRoot);

    _size+=2;
    newSubtreeRoot.expand();
    newSubtreeRoot.setRight(NBTsubtree);
    NBTsubtree.setParent(newSubtreeRoot);
    link(newSubtreeRoot.left(),newSibling);
  }

  /**
    * Takes O(S) time, where S is the number of positions in the new
    * subtree to graft on
    * You are only allowed to link in and replaceSubtree with other instances
    * of NodeBinaryTree (or subclasses thereof)
    */
  public void graftOnRight( Position subtree, Object eltOfParent, BinaryTree newSibling ){
    NBTNode NBTsubtree = checkPosition(subtree);

    NBTNode graftOnto = NBTsubtree.parent();
    NBTNode newSubtreeRoot = new NBTNode(graftOnto,eltOfParent);
    newSubtreeRoot.setContainer(this);

    if (graftOnto==_supernode)
      _supernode.setRoot(newSubtreeRoot);
    else
      graftOnto.setChild(NBTsubtree,newSubtreeRoot);

    _size+=2;
    newSubtreeRoot.expand();
    newSubtreeRoot.setLeft(NBTsubtree);
    NBTsubtree.setParent(newSubtreeRoot);
    link(newSubtreeRoot.right(),newSibling);
  }

  /**
    * O(1) time
    */
    public void expandExternal (Position mustBeExternal) throws
    InvalidAccessorException {
	NBTNode externalToExpand = checkPosition(mustBeExternal);
	if (externalToExpand.isInternal()) throw new InvalidAccessorException
					       ("You can't expand an internal node");
	externalToExpand.expand(); // now it's internal with two external children
	_size+=2;
    }

  /**
    * O(1) time
    */
    public void removeAboveExternal (Position mustBeExternal) throws
    InvalidAccessorException, BoundaryViolationException {
	NBTNode externalToRemove = checkPosition(mustBeExternal);
	if (isInternal(externalToRemove)) throw new InvalidAccessorException
		("You can't remove above an internal node");
	if (isRoot(externalToRemove)) throw new BoundaryViolationException
		("You can't remove above the root!");
	externalToRemove.removeSelfAndAbove();
	_size-=2;
    }
  
  /**
    * Takes O(S) time, where S is the number of positions in the subtree to cut
    */
    public BinaryTree cut (Position rootOfSubtree)throws InvalidAccessorException {
        // cutting means replacing the subtree with a leaf (i.e., with a newly
        // constructed tree)
        return replaceSubtree (rootOfSubtree,(BinaryTree)newContainer());
    }


  /**
    * Takes O(S) time, where S is the number of positions in this subtree
    * You are only allowed to link in and replaceSubtree with other instances
    * of NodeBinaryTree (or subclasses thereof)
    */
    public Object link (Position mustBeExternal, BinaryTree newSubtree)throws InvalidAccessorException, InvalidContainerException {
	NBTNode x = checkPosition (mustBeExternal);
        if (x.isInternal()) throw new InvalidAccessorException
					     ("You can't link at an internal node");
        replaceSubtree (mustBeExternal, newSubtree);
	return x.element();
    }


  /** 
    * Takes O(S1+S2) time, where S1 and S2 are the number of positions in each subtree
    * You are only allowed to link in and replaceSubtree with other instances
    * of NodeBinaryTree (or subclasses thereof)
    */
    public BinaryTree replaceSubtree (
            Position subtreeRoot,
            BinaryTree newSubtree)throws InvalidAccessorException, InvalidContainerException {
	if (newSubtree==this)
	  throw new InvalidContainerException("You can't link or replaceSubtree a tree into itself!");
	if ( ! (newSubtree instanceof NodeBinaryTree) || (newSubtree==null)) throw
					new InvalidContainerException
					("incompatible type of tree or null tree");

	

        NodeBinaryTree toSwapIn = (NodeBinaryTree) newSubtree;

	updateContainer((NBTNode)toSwapIn.root());

        // get the roots of the subtrees to be swapped
        NBTNode oldSubtreeRoot = checkPosition (subtreeRoot);
        NBTNode newSubtreeRoot = (NBTNode) toSwapIn.root();

	oldSubtreeRoot.replaceSelf (newSubtreeRoot);

        // make a new tree out of the nodes swapped out; the constructor
        // makes a new tree wrapper pointing to oldSubtreeRoot
        // and forces oldSubtreeRoot to point up to its new container
        NodeBinaryTree toReturn = new NodeBinaryTree
	    (oldSubtreeRoot);
	
	toReturn.updateContainer(toReturn.root());

        toSwapIn.resetToEmpty();

        return toReturn;
    }

  /**
    * Recursively changes the container of all nodes in the subtree
    * anchored at root to this container, adding to _size for each
    * node whose container we change
    * Takes O(S) time -- where S is the number of elements in the subtree
    * @param root The node to begin with
    */
  protected void updateContainer(Accessor root)throws InvalidAccessorException{
    NBTNode rootn = null;
    try{
      rootn = (NBTNode)root;
    }
    catch(ClassCastException cce){
      assert false : "Incompatible type of position";
    }
    _size++;
    if (rootn.container()!=null)
      rootn.container()._size--;
    rootn.setContainer(this);
    if (isInternal(rootn)){
      updateContainer(leftChild(rootn));
      updateContainer(rightChild(rootn));
    }
  }

    /**
     *--------------------------------------------------------
     * From interface InspectableBinaryTree
     *--------------------------------------------------------
     */

  /**
    * O(1) time
    */
    public Position leftChild (Position p) throws
    InvalidAccessorException, BoundaryViolationException {
	NBTNode check = checkPosition(p);
	if ( isExternal(check) ) throw new BoundaryViolationException
					("An external node has no children");
	return check.left(); 
    }
    
  /**
    * O(1) time
    */    
    public Position rightChild (Position p) throws
    InvalidAccessorException, BoundaryViolationException {
	NBTNode check = checkPosition(p);
	if ( isExternal(check) ) throw new BoundaryViolationException
					("An external node has no children");
	return check.right(); 
    }
    
  /**
   * O(1) time
   */    
  public Position sibling (Position p) throws
  InvalidAccessorException, BoundaryViolationException {
    PositionIterator pi = siblings(p);
    if (!pi.hasNext())
      throw new BoundaryViolationException("The root has no siblings");
    else
      return pi.nextPosition();
  }
    
    

    /**
     *--------------------------------------------------------  
     * From interface InspectableTree
     *--------------------------------------------------------
     */

  /**
    * O(1) time
    */ 
    public boolean isRoot (Position p) throws InvalidAccessorException {
        checkPosition (p);
        return ( p==root() );
    }

  /**
    * O(1) time
    */ 
    public boolean isInternal (Position p) throws InvalidAccessorException {
        NBTNode check = checkPosition(p);
        return check.isInternal();
    }

  /**
    * O(1) time
    */ 
    public boolean isExternal (Position p) throws InvalidAccessorException {
        return ! isInternal(p);
    }

  /**
    * O(1) time
    */ 
    public Position root() {
        return _supernode._root;
    }

  /**
    * O(1) time
    */ 
    public Position parent (Position p) throws
    InvalidAccessorException, BoundaryViolationException {
	NBTNode check = checkPosition(p);
	if (check==root()) throw new BoundaryViolationException
			       ("parent(root)");
	return check.parent();
    }
    
  /**
    * O(1) time
    */ 
    public PositionIterator children (Position p) throws
    InvalidAccessorException {
        NBTNode padre = checkPosition(p);
        if(isInternal(padre)) {
            Position [] kids = new Position[2];
            kids[0] = padre.left();
            kids[1] = padre.right();
            return new ArrayPositionIterator(kids);
        }
        else {
	  return new ArrayPositionIterator(null);//ext node has no children
        }
    }

  /**
    * O(1) time
    */ 
    public PositionIterator siblings (Position p) throws
    InvalidAccessorException {
      if (isRoot(p))
	throw new BoundaryViolationException("The root has no siblings");

      NBTNode n = checkPosition(p);
      Position [] sib = new Position[1];
      sib[0] = n.parent().otherChild(n);
      return new ArrayPositionIterator(sib);
    }

  /** 
    * O(1) time
    * Can be determined by the inherent nature of the type of node
    * rather than by counting
    */
  public int numChildren(Position node) throws InvalidAccessorException{
    checkPosition(node);
    if (isExternal(node))
      return 0;
    else
      return 2;
  }

  /**
    * O(1) time
    */ 
  public Position siblingAfter (Position node) throws
  BoundaryViolationException, InvalidAccessorException{
    
    NBTNode childnbt = checkPosition(node);

    if (childnbt.isLeftChild())
      return sibling(node);
    else
      if (isRoot(childnbt))
	throw new BoundaryViolationException("This is the root");
      else
	throw new BoundaryViolationException("This is the right child");
  }

  /**
    * O(1) time
    */ 
  public Position siblingBefore (Position node) throws
  BoundaryViolationException, InvalidAccessorException{
    
    NBTNode childnbt = checkPosition(node);

    if (!childnbt.isLeftChild())
      if (isRoot(childnbt))
	throw new BoundaryViolationException("This is the root");
      else
	return sibling(node);
    else
      throw new BoundaryViolationException("This is the left child");
  }
  
  /**
    * O(1) time
    */ 
  public Position firstChild (Position node) throws
  BoundaryViolationException, InvalidAccessorException{
    
    return childAtRank(node,0);
  }

  /**
    * O(1) time
    */ 
  public Position lastChild (Position node) throws
  BoundaryViolationException, InvalidAccessorException{
    
     return childAtRank(node,1);
  }
  
  /**
    * O(1) time
    */ 
  public int rankOfChild (Position child) throws
  BoundaryViolationException, InvalidAccessorException{
  
    NBTNode childnbt = checkPosition(child);

    if (childnbt.isLeftChild())
      return 0;
    else
      if (isRoot(childnbt))
	throw new BoundaryViolationException("This is the root");
      else
	return 1;
  }

  /**
    * O(1) time
    */ 
  public Position childAtRank (Position node, int rank) throws
  BoundaryViolationException, InvalidAccessorException{
  
    NBTNode parent = checkPosition(node);
    
    if (isExternal(parent))
      throw new BoundaryViolationException("This is an external node");

    if (rank == 0)
      return parent.left();
    if (rank == 1)
      return parent.right();

    throw new BoundaryViolationException("Rank "+rank+" is out of bounds -- Binary Trees only have children at ranks 0 and 1.");
      
  }

    /**
     *--------------------------------------------------------  
     * From interface [Inspectable]PositionalContainer
     *--------------------------------------------------------
     */


    /** 
      * Takes O(N) time from the need to iterate through the tree during 
      * snapshot, where N is the number of positions in the tree
     * @return PositionIterator of the container in preorder
     */
    public PositionIterator positions() {
	return new PreOrderIterator(this);
    }


  /** 
   * Takes O(N) time from the need to iterate through the tree during 
   * snapshot, where N is the number of elements in the tree
   * @return an iterator over the container's elements in preorder
   */
  public ObjectIterator elements() {
    PositionIterator pi = new PreOrderIterator(this);
    Object elements[] = new Object[size()];
    int elt = 0;
    while (pi.hasNext())
      elements[elt++] = pi.nextPosition().element();
    return new ArrayObjectIterator(elements);
  }


    /** 
     * O(1) time
     */
    public Object replaceElement (Accessor p, Object newElement) throws
    InvalidAccessorException {
	NBTNode toReplaceAt = checkPosition(p);
	return toReplaceAt.replaceElement (newElement);
    }
    

    /**
     *--------------------------------------------------------
     * From interface [Inspectable]Container
     *--------------------------------------------------------
     */

  /** 
     * O(1) time
     */
    public Container newContainer() {
        return new NodeBinaryTree();
    }

    /** 
     * O(1) time
     * @return Number of elements in the container, where each occurrence
     * of a duplicated element adds 1 to the size() of the container.
     */
    public int size() {
      return _size;
    }

    /** 
      * Overridden from AbstractPositionalContainer to be O(1) time.
     * Will always be false under the current definition of the
     * BinaryTree, since a BT is initialized with one external element.
     */
    public boolean isEmpty() {
        return false;
    }

  /**
    * O(1) time
    */
  public boolean contains(Accessor a){
    NBTNode nbtn = null;
    try{
      nbtn = (NBTNode) a;
      return (nbtn.container() == this);
    }
    catch(ClassCastException e){
      return false;
    }
    catch(NullPointerException e){
      throw new InvalidAccessorException("Null position cannot be contained");
    }
  }
  
  public String toString(){

    return ToString.stringfor(this);
  }

    //--------------------------------------------------
    // rest of class is utility methods

  /**
    * Used for resetting the tree to an empty tree after a link
    * or replaceSubtree operation.
    * This method is protected, so other trees can instruct
    * this tree to do so after a link or replaceSubtree operation
    * O(1) time
    */
  protected void resetToEmpty(){
      _supernode = new NBTSuperNode (this, null);
      NBTNode root = new NBTNode (_supernode, (Object)null);
      _size=1;
      _supernode.setRoot (root);
      root.setContainer(this);
  }

  /**
    * Casts the accessor passed in to the appropriate node class
    * for this container; also checks if it is null.
    * Also checks if it belongs to this container.
    *
    * This method is protected to allow it to be overridden to check
    * for container in a different fashion
    * 
    * @return The casted node
    * @param a The accessor to cast
    */
    protected NBTNode checkPosition (Accessor a) throws
    InvalidAccessorException {
	if (a==null) throw new InvalidAccessorException 
			 ("null position");

	if ( ! (a instanceof NBTNode) ) throw new InvalidAccessorException
					  ("position of wrong class: " + a.getClass());

	NBTNode n = (NBTNode) a;

	if (!(n.container()==this))
	  throw new InvalidAccessorException("A different container holds this NBTNode!");

	return n;
    }


  // -------------------------------------------------
  // two nested classes, for the nodes of the tree

  /**
   * This is the class for all user-visible nodes
   * It contains links for its parent, children, and element.
   * It determines its container by asking its parent; the
   * supernode will be at the end of a chain of parents, and it
   * will know. 
   * All methods must be protected so subclasses can override them
   */   
  protected static class NBTNode extends HashtableDecorable
    implements Position {

    /**
     * The parent of this node; never null while position is in tree
     * may be a supernode.
     * @serial
     */
    private NBTNode _parent; 

    /**
     * This node's left child. If this node is external, _left == null
     * @serial
     */
    private NBTNode _left;
    
    /**
     * This node's right child. If this node is external, _right== null
     * @serial
     */ 
    private NBTNode _right;
    
    /**
     * This node's container
     * @serial
     */ 
    private NodeBinaryTree _container;

    /**
     * This node's element. May be null.
     * @serial
     */ 
    private Object _element;
    
    // methods of Position interface
    
    /**
     * O(1) time
     */
    public Object element() {
      return _element;
    }

    /**
     * O(1) time
     * @return  this node's container.
     */
    protected NodeBinaryTree container() {
      return _container;
    }
    
    /**
     * O(1) time
     * @return  this node's parent.
     */
    protected NBTNode parent() { return _parent; }
    
    /**
     * O(1) time
     * @return  this node's left child.
     */
    protected NBTNode left() { return _left; }
    
    /**
     * O(1) time
     * @return this node's right child.
     */
    protected NBTNode right() { return _right; }
    
    /**
     * O(1) time
     * @param child of my children
     * @return  my other child
     * (asserts if the parameter isn't my child)
     */
    protected NBTNode otherChild (NBTNode child) {
      assert _left != null;
      if (child==_left) return _right;
      if (child==_right) return _left;
      assert false : "sibling( node that isn't my child )";
      return null; // compiler isn't quite that smart
    }


    /**
     * O(1) time
     * @return Whether or not this node is internal
     */
    protected boolean isInternal() { return _left != null; }

    /**
     * O(1) time
     * Sets the parameter node as this node's left child
     * @param x node
     */
    protected void setLeft (NBTNode x) { _left = x; }

    /**
     * O(1) time
     * Sets the parameter node as this node's right child
     * @param x node
     */
    protected void setRight (NBTNode x) { _right = x; }

    /**
     * O(1) time
     * Sets the parameter node as this node's parent
     * @param x node
     */
    protected void setParent (NBTNode x) { _parent = x; }

    /**
     * O(1) time
     * Sets the parameter container as this node's container
     */
    protected void setContainer (NodeBinaryTree x) { _container = x; }
	
    /**
     * O(1) time
     * @return whether or not this node is its parent's left child
     */
    protected boolean isLeftChild(){
      if (_parent.isSuperNode())
	return false; // I'm the root!
      if (_parent.left() == this)
	return true;//I'm the left child!
      return false;//I'm the right child!
    }

    /**	
     * O(1) time
     * Makes this node uncontained
     */
    protected void makeUncontained() {
      _container = null; 
      _parent = null; 
      _left = _right = null;
    }

    /**
     * make a new external node
     */
    protected NBTNode (NBTNode parent, Object element) {
      _parent = parent;
      _element = element;
      _left = _right = null;
    }

    /**	
     * O(1) time
     * Expands this node into an internal node
     * Asserts if this node is external
     */
    protected void expand() {
      assert !isInternal();
      _left = new NBTNode (this, (Object)null);
      _left.setContainer(_container);
      _right = new NBTNode (this, (Object)null);
      _right.setContainer(_container);
    }

    /**	
     * O(1) time
     * This method removes this node and its parent, replacing
     * its parent with my sibling
     *
     * This is the asymmetric opposite of expand.
     */
    protected void removeSelfAndAbove() { // asymmetric opposite of expand()
      assert _parent!=null : "removeSelfAndAbove on invalid node";
      assert _left==null : "removeSelfAndAbove() on non-leaf";
      NBTNode gp = _parent.parent();
      NBTNode sib = _parent.otherChild (this);
      gp.setChild (_parent, sib);
      sib.setParent(gp);
      _parent.makeUncontained();
      this.makeUncontained();
    }

    /**	
     * O(1) time
     * Replaces one of my children with a new node
     * protected to allow SuperNode to override it
     * @param currchild My current child
     * @param newchild The node to replace it with
     */
    protected void setChild (NBTNode currchild, NBTNode newchild) {
      if (_left==currchild) {
	_left = newchild;
      }
      else if (_right==currchild) {
	_right = newchild;
      }
      else assert false : "Asked to setChild on not-my-child";
    }


    /**	
     * O(1) time
     * Replaces me with a new node, as far as my parent is concerned
     * protected so restructurable trees can use it
     * @param newSubtree the node to replace me with
     */
    protected void replaceSelf (NBTNode newSubtree) {
      _parent.setChild (this, newSubtree);
      newSubtree.setParent (_parent);
      _parent = null; 
    }


    /**	
     * O(1) time
     * Replaces my element, returning the old element
     * @param newElement my new element
     * @return The element I used to contain
     */
    protected Object replaceElement (Object newElement) {
      Object toReturn = _element;
      _element = newElement;
      return toReturn;	  
    }
	
    /**
     * Used to determine if this node is the super node 
     */
    protected boolean isSuperNode(){
      return false;
    }

    public String toString(){
      return ToString.stringfor(this);
    }
  } 

  
  /**
   * This is the supernode.
   * There is one instance per tree, useful mainly so that container() calls
   * can recur polymorphically up the tree
   * Protected so subclasses can access it
   */
  protected static class NBTSuperNode extends NBTNode {
    
    /**
     * The tree that contains me
     * @serial
     */
    private NodeBinaryTree _tree;
    
    /**
     * That tree's root
     * @serial
     */
    private NBTNode _root;
    
    /**
     * Constructs the super node with its tree and root
     */
    protected NBTSuperNode (NodeBinaryTree t, NBTNode root) {
      super (null, (Object)null);
      _tree = t;
      _root = root;
    }
    
    /**
     * O(1) time
     * Sets this node's root
     * @param root The new root
     */ 
    protected void setRoot (NBTNode root) { 
      _root = root;
    }
    
    /**
     * O(1) time
     * Sets this node's root; any other use of this method is invalid
     * @param currchild The node to replace; hopefully the root
     * @param newchild The new root
     */ 
    protected void setChild (NBTNode currchild, NBTNode newchild) {
      assert _root==currchild;
      _root = newchild;
    }
    
    /**
     * @return this node's container
     */
    protected NodeBinaryTree container() {
      assert false; return null;
    }
    /**
     * Should never be called
     */
    public Object element() { assert false; return null; }
    /**
     * Should never be called
     */
    protected boolean isValid() { assert false; return false; }
    /**
     * Should never be called
     */
    protected NBTNode parent() { assert false; return null; }
    /**
     * Should never be called
     */
    protected NBTNode left() { assert false; return null; }
    /**
     * Should never be called
     */
    protected NBTNode right() { assert false; return null; }
    /**
     * Should never be called
     */
    protected NBTNode otherChild(NBTNode child) {
      assert false; return null;
    }
    /**
     * Should never be called
     */
    protected boolean isInternal() { assert false; return false; }
    /**
     * Should never be called
     */
    protected void setLeft() { assert false; }
    /**
     * Should never be called
     */
    protected void setRight() { assert false; }
    /**
     * Should never be called
     */
    protected void setParent() { assert false; }
    /**
     * Should never be called
     */
    protected void makeUncontained() { assert false; }
    /**
     * Should never be called
     */
    protected void expand()  { assert false; }
    /**
     * Should never be called
     */
    protected void removeSelfAndAbove() { assert false; }
    /**
     * Should never be called
     */
    protected void replaceSelf(NBTNode x) { assert false; }
    /**
     * Should never be called
     */
    protected void swapWithNode (NBTNode x) { assert false; }
    /**
     * Should never be called
     */
    protected Object replaceElement (Object x) {
      assert false; return null;
    }
    /**
     * Used to determine if this node is the super node (overridden)
     */
    protected boolean isSuperNode(){
      return true;
    }
  }
  // class NBTSuperNode
  
  // end of nested classes
  // -------------------------------------------------


}

