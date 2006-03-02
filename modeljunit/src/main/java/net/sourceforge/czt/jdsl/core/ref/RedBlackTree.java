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
 * A Dictionary implemented as a red-black tree.  (A red-black tree is
 * a balanced search tree that maintains its balance through coloring
 * its nodes. See "Data Structures and Algorithms in Java", Goodrich,
 * Tamassia, 2nd Ed., Ch.9.)  The red-black tree, in turn, is
 * implemented on top of a subclass of BinaryTree that has the ability
 * to rotate (restructure).
 *
 * This RB tree begins empty, and its internal structure can be accessed
 * with the inspectableBinaryTree method. Once the comparator is set,
 * it can never be changed.
 *
 * Leaf nodes contain locators with a null key; this separates them
 * from data nodes, which are internal and have locators with
 * legitimate, user's keys.
 * A position's color is represented in the locator it holds rather
 * than through a decoration, for faster access.
 *
 * The iterator-returning methods are not cached.
 *
 * This OrderedDictionary is a multi-map, meaning that it is possible
 * for two elements to have the same key.
 *
 * Currently has RestructurableNodeBinaryTree as a nested class while
 * waiting for a test for RNBT.
 *
 * @author Ming En Cho
 * @author Michael Boilen
 * @author Mark Handy
 * @author Ryan Shaun Baker
 * @author Luca Vismara
 * @version JDSL 2.1.1 
 *
 */
public class RedBlackTree implements OrderedDictionary {

  public static final int RED = 0;
  public static final int BLACK = 1;
  public static final int DOUBLEBLACK = 2;

  /**
   * Underlying tree
   */
  private RestructurableNodeBinaryTree tree_;

  /**
   * The comparator for the Dictionary
   */
  private Comparator comparator_;

  /**
   * The size (cached for O(1) access)
   */
  private int size_;
    
  /**
   * The one instance of a BlackColorHolder; held by
   * all black external nodes
   */
  private BlackColorHolder bch_ = new BlackColorHolder();

  /**
   * The one instance of a DoubleBlackColorHolder; held by
   * all double- black external nodes
   * (should only be one at a time)
   */
  private DoubleBlackColorHolder dbch_ = new DoubleBlackColorHolder();

  
  /**
   *  Takes O(1) time
   *  This constructor creates the tree with a single 
   *  no-element-stored-here locator. (null key)
   */
  public RedBlackTree (Comparator comparator) {
    tree_ = new RestructurableNodeBinaryTree();
    comparator_ = comparator;
    tree_.replaceElement(tree_.root(), bch_);
  }

  
  // Container/InspectableContainer methods

  /** 
   * Takes O(1) time
   */
  public Container newContainer() {
    return new RedBlackTree(comparator_);
  }

  
  /** 
   * Takes O(1) time
   */
  public int size() { return size_; }

  
  /** 
   * Takes O(1) time
   */
  public boolean isEmpty() { return size_==0; }

  
  /** 
   * Takes O(1) time
   */
  public boolean contains (Accessor a) throws InvalidAccessorException{
    if (a == null)
      throw new InvalidAccessorException
	("No container contains a null accessor");
    if ((!(a instanceof RBTLocator)) || (((RBTLocator)a).container() != this))
      return false;
    return true;
  }

  
  /** 
   * Takes O(1) time
   */
  public Object replaceElement (Accessor loc, Object newElement) throws
  InvalidAccessorException {
    RBTLocator ul = checkLocator (loc);
    Object oldel = ul.element();
    ul.setElement(newElement);
    return oldel;
  }


  // IKBC/KBC methods  

  /** 
   * Takes O(N) time from the need to iterate through the tree during 
   * snapshot -- where N= the number of locators in the tree
   *
   * Could very easily be cached; not sure that would be useful
   *
   * @return LocatorIterator of the container inorder
   */
  public LocatorIterator locators() {
    PositionIterator pi = new InOrderIterator(tree_);

    Locator[] locarray = new Locator[size()];

    int i = 0;
    while (pi.hasNext()){
      pi.nextPosition();
      if (pi.element() instanceof Locator){
	locarray[i++] = (Locator)(pi.element());
      }
    }
    ArrayLocatorIterator akbi = new ArrayLocatorIterator(locarray,i);

    return akbi;
  }

  
  /** 
   * Takes O(N) time from the need to iterate through the tree during 
   * snapshot -- where N= the number of locators in the tree
   *
   * Could very easily be cached; not sure that would be useful
   *
   * @return an iterator over the container elements inorder
   */
  public ObjectIterator elements() {
    LocatorIterator akbi = locators();

    Object elements[] = new Object[size()];
    int elt = 0;
    while (akbi.hasNext())
      elements[elt++] = akbi.nextLocator().element();
    return new ArrayObjectIterator(elements);

  }

  
  /** 
   * Takes O(N) time from the need to iterate through the tree during 
   * snapshot -- where N= the number of locators in the tree
   *
   * Could very easily be cached; not sure that would be useful
   *
   * @return an iterator over the container keys inorder
   */
  public ObjectIterator keys() {
    LocatorIterator akbi = locators();

    Object keys[] = new Object[size()];
    int key = 0;
    while (akbi.hasNext()){
      akbi.nextLocator();
      keys[key++] = akbi.key();
    }
    return new ArrayObjectIterator(keys);

  }

  
  /** 
   * Takes O(logN) time -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * Takes the running time it would take to execute
   * both remove and insert.
   */
  public Object replaceKey(Locator locator, Object key) throws
  InvalidAccessorException, InvalidKeyException {
    if (!comparator_.isComparable(key))
      throw new InvalidKeyException("replacement key is not comparable");
    RBTLocator ul = checkLocator (locator);
    Object oldKey = ul.key();
    remove(locator);
    ul.setKey(key);
    insertLoc (locator);
    return oldKey;
  }

  
  /** 
   * Takes O(logN) time  -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * Takes the time to traverse the tree's height, which is O(logN)
   */
  public Locator find(Object key) throws InvalidKeyException {
    if ( ! comparator_.isComparable(key))
      throw new InvalidKeyException
	("Key requested not comparable with existing keys");
    Position found = findInSubtree(key, tree_.root());
    if (tree_.isExternal(found))
      return NO_SUCH_KEY;
//     return checkLocator(found.element());
    return (RBTLocator)found.element();
  }

  
  /** 
   * Takes O(logN+R) time -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree, and R = the number of 
   * instances of key in the tree
   *
   * O(log N) for one element; in theory, for each element, taking its inorder
   * prev or next may take up to O(log N). In practice, the O(log N) case
   * can only occur twice, and every other case is O(1).
   */
  public LocatorIterator findAll(Object key) throws InvalidKeyException {
    Locator[] toret = new Locator[size()]; // accumulate results
    int actualnum = 0;
	
    if ( ! comparator_.isComparable(key))
      throw new InvalidKeyException
	("Key requested not comparable with existing keys");

    // first try to find a matching key (the one at the root of the subtree
    // containing all the keys), then traverse backward and forward
    // from there until we exit the range of matching keys
    Position p = findInSubtree (key, tree_.root());
    if (tree_.isExternal(p))
      return new ArrayLocatorIterator(toret,actualnum);// key not found
	
    Position first = tree_.leftChild(((RBTLocator)first()).treePosition()); // a leaf node
    Position last = tree_.rightChild(((RBTLocator)last()).treePosition()); // a leaf node
//     RBTLocator h = checkLocator(p.element());
    RBTLocator h = (RBTLocator)p.element();

    Position save = p; //save where we started from

    //first check to the right
    while (comparator_.isEqualTo(h.key(),key)){
      toret[actualnum++] = h;
      // next() alternates between leaves and internals
      p = next(p);
      if (p==last) break;
      p = next(p);
//       h = checkLocator (p.element());
      h = (RBTLocator)p.element();
    }
    // now check to the left
    p = prev(save);
    if (p==first) return new ArrayLocatorIterator(toret,actualnum);
    p = prev(p);
//     h = checkLocator (p.element());
    h = (RBTLocator)p.element();
    while (comparator_.isEqualTo(h.key(),key)){
      toret[actualnum++] = h;
      p = prev(p);
      if (p==first) return new ArrayLocatorIterator(toret,actualnum);
      p = prev(p);
//       h = checkLocator (p.element());
      h = (RBTLocator)p.element();
    }
    return new ArrayLocatorIterator(toret,actualnum);
  }

  
  /**
   * Takes O(logN) time  -- traverses the height of the tree once.
   */
  public Locator closestBefore(Object key) throws InvalidKeyException { 
    if (!comparator_.isComparable(key))
      throw new InvalidKeyException
	("This key is inappropriate for this structure's comparator");
    if(isEmpty()) return BOUNDARY_VIOLATION;
    Position found=findInSubtree(key, tree_.root());
    if (tree_.isInternal(found))
//       return checkLocator(found.element());
      return (RBTLocator)found.element();
//     if (found==(tree_.leftChild(checkLocator(first()).treePosition())))
    if (found == tree_.leftChild(((RBTLocator)first()).treePosition()))
      return BOUNDARY_VIOLATION;
//     return checkLocator(prev(found).element());
    return (RBTLocator)prev(found).element();
  }

  
  /**
   * Takes O(logN) time  -- traverses the height of the tree once.
   */
  public Locator closestAfter(Object key) throws InvalidKeyException {
    if (!comparator_.isComparable(key))
      throw new InvalidKeyException
	("This key is inappropriate for this structure's comparator");
    if(isEmpty()) return BOUNDARY_VIOLATION;
    Position found=findInSubtree(key, tree_.root());
    if (tree_.isInternal(found))
//       return checkLocator(found.element());
      return (RBTLocator)found.element();
//     if (found==(tree_.rightChild(checkLocator(last()).treePosition())))
    if (found == tree_.rightChild(((RBTLocator)last()).treePosition()))
      return BOUNDARY_VIOLATION;
//     return checkLocator(next(found).element());
    return (RBTLocator)next(found).element();
  }

  
  /**
   * Takes O(logN) time -- may need to traverse the height of the tree
   * to find the next note that we do not return color-locators in the
   * leaves -- we only return key locators.
   */
  public Locator after(Locator locator) throws InvalidAccessorException {    
    Position p = checkLocator(locator).treePosition();
    // p is an internal (if there are no bugs...)
    p = next(p); // now points to a leaf
    try {
//       return checkLocator(next(p).element());
      return (RBTLocator)next(p).element();
    }
    catch (BoundaryViolationException bve) {
      return BOUNDARY_VIOLATION;
    }
  }

  
  /**
   * Takes O(logN) time -- may need to traverse the height of the tree
   * to find the next note that we do not return color-locators in the
   * leaves -- we only return key locators.
   */
  public Locator before(Locator locator) throws InvalidAccessorException {
    Position p = checkLocator(locator).treePosition();
    // p is an internal (if there are no bugs...)
    p = prev(p); // now points to a leaf
    try {
//       return checkLocator(prev(p).element());
      return (RBTLocator)prev(p).element();
    }
    catch (BoundaryViolationException bve) {
      return BOUNDARY_VIOLATION;
    }
  }

  
  /**
   * Takes O(logN) time  -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   * The worst-case insertion would restructure once each step up the tree.
   */    
  public Locator insert(Object key, Object element) throws
  InvalidKeyException {
    Locator toReturn = new RBTLocator(key,element,this,null);
    insertLoc (toReturn);
    return toReturn;
  }

  
  /**
   * Takes O(logN) time  -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * The worst-case insertion would restructure once each step up the tree.
   * Finds the proper BST place to put the new locator
   * Places it in colored red, and then checks if the tree
   * still maintains Red Black Tree properties; if not,
   * go to the insertion cases
   * This method is private, because we currently do not have the ability
   * to insert a free-floating locator in KBCs.
   *
   * @param loc The locator to insert
   */    
  private void insertLoc (Locator loc) throws InvalidKeyException,
  InvalidAccessorException {
    if (loc == null)
      throw new InvalidAccessorException("Null locator passed in.");
    RBTLocator rbtl = null;
    try{
      rbtl = (RBTLocator) loc;
    }
    catch (ClassCastException e){
      throw new InvalidAccessorException("Wrong type of locator passed in.");
    }
    if ( ! comparator_.isComparable(rbtl.key()))
      throw new InvalidKeyException("Key to insert is not comparable");
      
    // find a leaf at which to insert, expand the leaf, and do the deed
    Position p = findInSubtree(rbtl.key(), tree_.root());  
    if (tree_.isInternal(p)) {
      p = next(p);
    }
    tree_.expandExternal(p);
    tree_.replaceElement(p, rbtl);	
    rbtl.setContainer(this);
    rbtl.setPosition(p);
    makeRed(p);
      
    // color both new leaves black
    tree_.replaceElement(tree_.rightChild(p),bch_);
    tree_.replaceElement(tree_.leftChild(p), bch_);
      
    checkDoubleRed(p);

    // root should always be black 
    makeBlack (tree_.root());
      
    size_++;
  }

  
  /**
   * Takes O(logN) time  -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * Check for double reds, then rotate or promote if necessary
   * Protected for purposes of allowing snapshots during visualization
   * @param p The position that would be the child of the two double reds
   */
  protected void checkDoubleRed(Position p) {
    if (tree_.isRoot(p)) return; //the first node inserted can't have doublered
    Position parent = tree_.parent(p);
    if (tree_.isRoot(parent)) return; // the root will be made black in insertloc
    else if (isRed(parent)) { 
      Position uncle = tree_.sibling(parent);
      if (isRed(uncle)) {
	colorPromotion(parent,uncle);
      }
      else {
	// rotate and correct the colors, and we're done
	Position newroot = tree_.restructure(p);
	makeBlack (newroot);
	makeRed (tree_.leftChild(newroot));
	makeRed (tree_.rightChild(newroot));
      }
    }
  }

  
  /**
   * Takes O(logN) time -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * Do a color promotion and then check if colors are now wrong higher up   
   * Protected for purposes of allowing snapshots during visualization
   * @param parent The position that would be the parent of the two double reds
   * @param uncle parent's sibling
   */
  protected void colorPromotion(Position parent, Position uncle) {    
    makeBlack (parent);
    makeBlack (uncle);
    Position grandParent = tree_.parent(parent);
    makeRed (grandParent);
    //check for double red at the next level up
    checkDoubleRed(grandParent);
  }

  
  /**
   * Takes O(RlogN) time
   * where R = the number of objects with key key
   * and log N = the height of the tree (N locators in the tree)
   * (one removal case per each object)
   */ 
  public LocatorIterator removeAll (Object key) throws InvalidKeyException{
    LocatorIterator toret = findAll(key);
    while (toret.hasNext()) {
      remove(toret.nextLocator());
    }
    // since iterators have snapshot semantics, we can reuse toret
    toret.reset();
    return toret;
  }

  
  /**
   * Takes O(logN) time  -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * The worst-case removal would restructure once each step up the tree.
   * Finds the locator to remove, then removes it.
   */
  public Locator removeKey (Object key) throws InvalidKeyException{
    Locator toret = find(key);
    remove(toret);
    return toret;
  }

  
  /**
   * Takes O(logN) time  -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   *
   * The worst-case removal would restructure once each step up the tree.
   * 
   * Ensures that the locator has a leaf child (Swapping if necessary)
   * Then removes it. 
   * This leaves a double-black node, which we then resolve to a black node.
   * This may propagate the double-black up the tree, in which case
   * more resolutions will be necessary.
   * The number of resolutions (repairs to the tree) will be <= O(log N)
   *
   */
  public void remove (Locator locator) throws InvalidAccessorException {
    RBTLocator loc = checkLocator(locator);
    Position locpos = loc.treePosition();

    assert tree_.isInternal(locpos)
      : "Locator's position is an external -- indicates bug in r-b tree";

    // first need to assure that the position to be removed from the
    // tree is above a leaf.  Either it is already so or we have to swap
    // to make it so.
    Position leaf = null; 
	
    if ( tree_.isInternal(tree_.rightChild(locpos)) &&
	 tree_.isInternal(tree_.leftChild (locpos)) ) {
      // swap locpos with its predecessor internal node
      leaf = prev(locpos);
      Position swapwith = tree_.parent( leaf );
//       RBTLocator swapwithRBTLocator = checkLocator( swapwith.element() );
      RBTLocator swapwithRBTLocator = (RBTLocator)swapwith.element();

      // swap semantics: leave colors associated with their
      // tree positions while swapping the locators stored at the
      // positions.  But colors are implemented as being held by the
      // locators, so we swap locators, update locators' position-pointers
      // for consistency, then reswap the locators' colors.
      tree_.swapElements(locpos, swapwith); 
      swapwithRBTLocator.setPosition(locpos);
      loc.setPosition(swapwith);
      int tempColor = swapwithRBTLocator.color();
      swapwithRBTLocator.setColor(loc.color());
      loc.setColor(tempColor);
    }
    else 
      if (tree_.isExternal(tree_.leftChild(locpos))) 
	leaf = tree_.leftChild(locpos);
      else // right child must be external 
	leaf = tree_.rightChild(locpos);

    // now the locator to be removed is above a leaf, so we can 
    // remove above the leaf.
    // But first: leaf's sibling is either a leaf or a minimal subtree,
    // and it will move up a level to become locpos's parent's new child
    Position leafsib = tree_.sibling(leaf);
    tree_.removeAboveExternal(leaf);
	
    // if locpos was black (after any swap), then by removing it we 
    // decreased the black depth of the leaves in leafsib's subtree
    if (loc.color()==BLACK){ 
      recolorAfterRemove(leafsib);
    }
    makeBlack( tree_.root() ); 
    loc.setContainer(null);
    size_--;
  }
    

  /**
   * Takes O(logN) time -- where N = the number of locators in the
   * tree and O(logN) = the height of the tree.
   *
   * Recolors after removal, i.e., delegate to appropriate case; can
   * be called recursively for case 2.  Protected for purposes of
   * allowing snapshots during visualization
   *
   * @param p The node to recolor above
   */
  protected void recolorAfterRemove(Position p) {
      
    assert tree_.contains(p) : "Position is from the wrong tree";
      
    if ( (isBlack(p) || isDoubleBlack(p)) &&
	 ! tree_.isRoot(p) ) {

      // if p is black then
      // p's black depth is too low, so insert an illegal extra black
      // edge above p to restore p's black depth.  Then deal
      // with the illegal edge
	  
      makeDoubleBlack(p ); 

      //if sib is red, then case3 and continue to case 1 or case 2
      Position sibling = tree_.sibling(p);
      if (isRed(sibling)){
	case3( sibling );
	sibling = tree_.sibling(p);
      }
      if (isBlack(sibling)) {
	Position parent = tree_.parent(p);
	Position sibLeft = tree_.leftChild(sibling);
	Position sibRight = tree_.rightChild(sibling);
		
	if (isBlack(sibLeft)&&isBlack(sibRight)) {
	  case2(sibling);
	  if (isDoubleBlack(parent))//still a double black to resolve
	    recolorAfterRemove(parent);
	}else
	  if (isBlack(sibRight)&&isRed(sibLeft)) 
	    case1(sibling,sibLeft);
	  else
	    case1(sibling,sibRight);
      }
    }
    else makeBlack( p );
  }

  
  /**
   * Takes O(1) time
   * Implements case 1, the Restructuring case
   *
   * Protected for purposes of allowing snapshots during visualization
   *
   * @param y -- the sibling of the double-black node
   * @param z -- the red child of y
   */
  protected void case1(Position y, Position z){
    assert tree_.contains(y) && tree_.contains(z)
      : "Position is from the wrong tree";

    Position x = tree_.parent(y);// The parent of the double-black node
    Position r = tree_.sibling(y);//The double-black node

//     int xcolor = checkLocator((Locator)x.element()).color();
    int xcolor = ((RBTLocator)x.element()).color();

    Position b = tree_.restructure(z);// The root of the restructured subtree
    Position a = tree_.leftChild(b);
    Position c = tree_.rightChild(b);

    makeBlack(a);
    makeBlack(c);

//     checkLocator((Locator)b.element()).setColor(xcolor);
    ((RBTLocator)b.element()).setColor(xcolor);
    makeBlack(r);
  }


  /**
   * Takes O(1) time
   * Implements case 2, the Recoloring case
   *
   * Protected for purposes of allowing snapshots during visualization
   * @param y -- the sibling of the double-black node
   */
  protected void case2(Position y){     
    assert tree_.contains(y) : "Position is from the wrong tree";

    Position x = tree_.parent(y);// The parent of the double-black node
    Position r = tree_.sibling(y);//The double-black node

    makeBlack(r);
    makeRed(y);
    if (isRed(x))
      makeBlack(x);
    else
      makeDoubleBlack(x);
  }

  
  /**
   * Takes O(1) time
   * Implements case 3, the Adjustment case    
   * Protected for purposes of allowing snapshots during visualization
   *
   * @param y -- the sibling of the double-black node
   */
  protected void case3(Position y){
    assert tree_.contains(y) : "Position is from the wrong tree";

    Position x = tree_.parent(y);// The parent of the double-black node
    Position z = null;
    if (tree_.rightChild(x)==y)
      z = tree_.rightChild(y);
    else
      z = tree_.leftChild(y);

    tree_.restructure(z);

    makeBlack(y);
    makeRed(x);
  }


  /**
   * Takes O(log N) time -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   * Moves the current node forward, in order
   * @return Inorder-next of the current node.
   * @exception BoundaryViolationException If the given node is last
   * @param current The position to take the next of
   */
  private Position next(Position current) throws BoundaryViolationException {
    if (tree_.isExternal(current)){
      if (current == tree_.root())
	throw new BoundaryViolationException("Empty tree");
      if  (tree_.leftChild(tree_.parent(current)) == current){
	current = tree_.parent(current);
      }
      else {
	boolean founduncle = false;
	while (!founduncle){
	  current = tree_.parent(current);
	  if (tree_.leftChild(tree_.parent(current)) == current)
	    founduncle = true;
	  if (current == tree_.root())
	    throw new BoundaryViolationException("Empty tree");
	}
	current = tree_.parent(current);
      }
    }
    else {
      current = tree_.rightChild(current);
      while (!tree_.isExternal(current))
	current = tree_.leftChild(current);
    }
    return (current);
  }
    
    
  /**
   * Takes O(log N) time -- where N = the number of locators in the tree
   * and O(logN) = the height of the tree
   * Moves the current node backward, relative to an in-order ordering
   * of the nodes.
   * @return the in-order-previous of the current position, including
   * the leaves
   * @exception BoundaryViolationException If the given node is last
   * @param current The position to take the prev of
   */
  private Position prev(Position current) throws BoundaryViolationException {
    if (tree_.isExternal(current)) {
      if (current == tree_.root())
	throw new BoundaryViolationException("Empty tree");
      if  (tree_.rightChild(tree_.parent(current)) == current){
	current = tree_.parent(current);
      }
      else{
	boolean founduncle = false;
	while (!founduncle){
	  current = tree_.parent(current);
	  if (tree_.rightChild(tree_.parent(current)) == current)
	    founduncle = true;
	  if (current == tree_.root())
	    throw new BoundaryViolationException("Empty tree");
	}
	current = tree_.parent(current);
      }
    }
    else {
      current = tree_.leftChild(current);
      while (!tree_.isExternal(current))
	current = tree_.rightChild(current);
    }
    return (current);	
  }

  
  /**
   * Takes O(log N) time to traverse the height of the tree
   * where N is the number of locators in the tree and O(logN) is
   * the height of the tree
   */
  public Locator first(){
    Locator before = InspectableOrderedDictionary.BOUNDARY_VIOLATION;
    Position cur = tree_.root();
    while (!tree_.isExternal(cur)){
//       before = checkLocator(cur.element());
      before = (RBTLocator)cur.element();
      cur = tree_.leftChild(cur);
    }
    return before;
  }

  
  /**
   * Takes O(log N) time to traverse the height of the tree
   * where N is the number of locators in the tree and O(logN) is
   * the height of the tree
   */
  public Locator last(){
    Locator before = InspectableOrderedDictionary.BOUNDARY_VIOLATION;
    Position cur = tree_.root();
    while (!tree_.isExternal(cur)){
//       before = checkLocator(cur.element());
      before = (RBTLocator)cur.element();
      cur = tree_.rightChild(cur);
    }
    return before;
  }

  
  /**
   * Takes O(1) time
   * Convenience method for casting an  element of the underlying
   * tree, which should be a ColorHolder
   */
//   private ColorHolder checkHolder(Object treeElement) throws
//   InvalidAccessorException {
//     if (treeElement == null)
//       throw new InvalidMethodCallException
// 	("Tree element (ColorHolder) is null");
//     try{
//       return (ColorHolder) treeElement;
//     }
//     catch(ClassCastException cce) {
//       throw new InvalidMethodCallException("Tree element not a ColorHolder");
//     }
//   }

  
  /**
   * Takes O(1) time
   * Safety method for checking a locator given to us by the user
   * (checks whether this is its container)
   *
   * @param a The accessor
   * @return The casted RBTLocator
   */
  private RBTLocator checkLocator (Object a) throws
  InvalidAccessorException {
    if (a == null)
      throw new InvalidAccessorException("Locator is null");
    if (!(a instanceof RBTLocator))
      throw new InvalidAccessorException("Not a Locator");

    RBTLocator rbtl = (RBTLocator)a;

    if (rbtl.container() != this)
      throw new InvalidAccessorException("Locator from a different container");
    return rbtl;
  }


  /**
   * Takes O(log N) time -- where N = the number of locators in the
   * tree and O(logN) = the height of the tree -- may traverse down
   * the height one path
   *
   * Service method to search underlying tree recursively
   *
   * @param key Key to search for
   * @param subtreeRoot The subtree to search in
   */
  private Position findInSubtree(Object key, Position subtreeRoot) throws
  InvalidKeyException{
    Position node = subtreeRoot;

//     if (tree_.isExternal(subtreeRoot))
//       return subtreeRoot;
//     // search here first, then left or right if necessary
//     Object rootKey = checkLocator(subtreeRoot.element()) . key();
//     if (comparator_.isEqualTo(key, rootKey))
//       return subtreeRoot;
//     if (comparator_.isGreaterThan(key,rootKey))
//       return findInSubtree(key,tree_.rightChild(subtreeRoot));
//     else
//       return findInSubtree(key, tree_.leftChild(subtreeRoot));

    while (tree_.isInternal(node)) {
//       Object nodeKey = checkLocator(node.element()).key();
      Object nodeKey = ((RBTLocator)node.element()).key();
      int result = comparator_.compare(key,nodeKey);
      if (result == 0)
	break;
      else if (result < 0)
	node = tree_.leftChild(node);
      else
	node = tree_.rightChild(node);
    }
    return node;
  }

  
  // convenience methods for dealing with the fact that colors conceptually
  // belong to positions of the underlying tree, but in implementation
  // colors are stored by locators

  /**
   * Returns whether or not the given position of the underlying tre
   * is red; for visualization/testing purposes.
   *
   * @param p The position to check
   */
  public final boolean isRed (Position p) {
//     return checkHolder(p.element()).color()==RED;
    return ((ColorHolder)p.element()).color() == RED;
  }

  
  /**
   * Returns whether or not the given position of the underlying tre
   * is black; for visualization/testing purposes.
   *
   * @param p The position to check
   */
  public final boolean isBlack (Position p) {
//     return checkHolder(p.element()).color()==BLACK;
    return ((ColorHolder)p.element()).color() == BLACK;
  }

  
  /**
   * Returns whether or not the given position of the underlying tre
   * is double-black; for visualization/testing purposes.
   *
   * @param p The position to check
   */
  public final boolean isDoubleBlack (Position p) {
//     return checkHolder(p.element()).color()==DOUBLEBLACK;
    return ((ColorHolder)p.element()).color() == DOUBLEBLACK;
  }

  
  private final void makeRed (Position p) {
    assert tree_.isInternal(p) : "External nodes should never be red!";
//     checkLocator (p.element()).setColor(RED);
    ((RBTLocator)p.element()).setColor(RED);
  }

  
  private final void makeBlack (Position p) {
    if (tree_.isExternal(p))
      tree_.replaceElement(p,bch_);
    else
//       checkLocator (p.element()).setColor (BLACK);
      ((RBTLocator)p.element()).setColor(BLACK);
  }

  
  private final void makeDoubleBlack (Position p) {
    if (tree_.isExternal(p))	
      tree_.replaceElement(p,dbch_);
    else
//       checkLocator (p.element()).setColor (DOUBLEBLACK);
      ((RBTLocator)p.element()).setColor(DOUBLEBLACK);
  }


  /**
   * Used for visualization and testers
   */
  public InspectableBinaryTree inspectableBinaryTree(){
    return tree_;
  }

  
  public String toString(){
    return ToString.stringfor(this);
  }

  
  /**
   * Any class implementing this interface has a color. Positions are colored
   * by placing an implementation of this class in their element.
   */
  private static interface ColorHolder{      
    /**
     * Package-friendly because the compiler doesn't allow private interface
     * methods
     * @return my position's color
     */
    int color();
  }

  
  /**
   * The color holder for black external positions
   */
  private static class BlackColorHolder implements ColorHolder{
    
    /**
     * Takes O(1) time
     * @return my position's color -- BLACK
     */
    public final int color(){ return BLACK;}

  }


  /**
   * The color holder for double-black external positions
   */
  private static class DoubleBlackColorHolder implements ColorHolder{
    
    /**
     * Takes O(1) time
     * @return my position's color -- DOUBLEBLACK
     */
    public final int color(){ return DOUBLEBLACK;}

  }


  /**
   * Data-holder class: holds color, key, and position in underlying tree,
   * plus administrative info.  
   * <p>
   */
  private static class RBTLocator implements Locator, ColorHolder{
      
    /**
     * The color of the position this holder is in
     */
    private int color_ = RED;

    /**
     * The tree position this color holder is associated with
     */
    private Position treepos_;

    /**
     * This locator's key
     */
    private Object key_;

    /**
     * This locator's element
     */
    private Object element_;

    /**
     * This locator's container
     */
    private RedBlackTree container_;

    
    /**
     * Takes O(1) time
     * A constructor for setting all RBTLocator fields
     */
    private RBTLocator(Object key, Object element,
		       RedBlackTree container, Position position) {
      key_ = key;
      element_ = element;
      container_ = container;
      treepos_ = position;
    }

    
    /**
     * Takes O(1) time
     *  @return  this node's container.
     */
    private final InspectableContainer container(){
      return container_;
    }

    
    /**
     * Takes O(1) time
     *  @param container this node's new container.
     */
    private final void setContainer(RedBlackTree container){
      container_ = container;
    }

    
    /**
     * Takes O(1) time
     */
    public final Object element(){
      return element_;
    }

    
    /**	
     * Takes O(1) time
     * Replaces my element
     * @param element my new element
     */
    private final void setElement(Object element) { element_ = element; }

    
    /**
     * Takes O(1) time
     * @return my key
     */	
    public final Object key() { return key_; }

    
    /**	
     * Takes O(1) time
     * Sets my key
     * @param key my new key
     */
    private final void setKey(Object key) { key_ = key; }

    
    /**
     * Takes O(1) time
     * @return my position in the tree
     */
    private final Position treePosition() { return treepos_; }

    
    /**
     * Takes O(1) time
     * Sets my position in the tree
     * @param position my new position
     */
    private final void setPosition(Position position) {treepos_ = position;}

    
    /**
     * Takes O(1) time
     * protected so subclass can print out in toString
     * @return my position's color
     */
    public final int color() { return color_; }

    
    /**
     * Takes O(1) time
     * protected so classes using my subclass can use me
     * Sets my position's color
     * @param color my new color
     */
    private final void setColor(int color) { color_ = color; }

    
    public String toString(){
      return ToString.stringfor(this);
    }

  } // end of RBTLocator class def


  
  /**
   * A <code>BinaryTree</code> that supports AVL/RedBlack Tree restructuring. 
   * (also known as Tree Rotation -- see Goodrich,Tamassia ch.7) 
   * Has its own cut/link/replaceSubtree to keep operations O(1)
   * with underscores to denote the O(1) versions
   * (we can be free of the responsibility to do container modifications
   * because we are modifying only within our own structure)
   * Note that no external classes may call the O(1) versions; for
   * security, they must call the O(N) versions.
   * All other methods function as previous
   *
 * @author Ming-En Cho (mec)
 * @author Mike Boilen (mgb)
 * @author Mark Handy (mdh)
 * @author Ryan Shaun Baker (rsb)
   * @version JDSL 2.1.1 
   */
  private static class RestructurableNodeBinaryTree extends NodeBinaryTree {

    // used as globals during restructure(.)
    private Position grandchild_;
    private Position parent_;
    private Position grandparent_;
    protected boolean restructuring_ = false;

    
    public RestructurableNodeBinaryTree(){
      super();
    }

    
    protected RestructurableNodeBinaryTree(NBTNode n){
      super(n);
    }

    
    /**
     *
     * O(1)
     *
     * Performs a rotation (restructuring) of the following three nodes:
     * the node specified, its parent, and its grandparent.  The node
     * specified (call it x) winds up one or two levels closer to the root,
     * but the inorder traversal of the entire tree is unaffected. Takes
     * constant time, assuming that cut(.) and link(.) take constant time.
     *
     * The algorithm is <br>
     * <ol>
     * <li>detach the subtree rooted at grandparent from the main tree
     * <li>detach the four uninvolved subtrees (one child of grandparent,
     * one child of parent, both children of x)
     * <li> perform an inorder traversal on the resulting minitree (the
     * three involved nodes and the four vestigial leaves)
     * <li> cut the minitree apart and reassemble it so that the inorder-median
     * of the three involved nodes is the new root of the minitree
     * <li> put back the snipped-off subtrees, in order (they won't necessarily
     * reattach to their original parents)
     * <li> reattach the rotated subtree to the main tree, in the same place.
     * </ol>
     *
     * (see Goodrich,Tamassia ch.7)
     *
     * @param grandchild The position to rotate at.
     * @exception BoundaryViolationException if grandchild does not have a 
     * grandparent -- taking the rotation above the root -- or on the attempt 
     * to rotate around an external.
     * @exception InvalidAccessorException if <code>grandchild</code> is
     *  invalid
     */
    public Position restructure (Position grandchild) throws
    BoundaryViolationException, InvalidAccessorException {
	
      restructuring_ = true;

      if (isExternal(grandchild))
	throw new BoundaryViolationException("cannot rotate on an external");
	
      //positions involved in this rotation
      grandchild_ = grandchild;
      parent_ = parent(grandchild);
      grandparent_ = parent(parent_);

      // used later, to know where to reattach the rotated subtree
      // to the main tree
      boolean gparentIsRoot = isRoot(grandparent_);
      boolean gparentIsRightChild = false;
      Position ggparent = null;
      if (! gparentIsRoot) {
	ggparent = parent(grandparent_);
	if (rightChild(ggparent)==grandparent_)
	  gparentIsRightChild=true;
      }
	
      // cut off all of the subtrees that aren't involved in the rotation,
      // and cut the involved subtree off from the main tree
      RestructurableNodeBinaryTree subtree =  pruneSubtree();

      //traverse the tree, to find the order of the subtrees
      InOrderIterator iterator = new InOrderIterator(subtree);
	
      //cut apart the subtree

      iterator.nextPosition();
      Position zero  = iterator.position();
      iterator.nextPosition();
      Position left = iterator.position();	
      iterator.nextPosition();
      Position two = iterator.position();	
      iterator.nextPosition();
      Position center = iterator.position();	
      iterator.nextPosition();
      Position four = iterator.position();	
      iterator.nextPosition();
      Position right = iterator.position();	
      iterator.nextPosition();
      Position six = iterator.position();	

      RestructurableNodeBinaryTree grandchildTree = subtree._cut(grandchild_);
      RestructurableNodeBinaryTree parentTree = subtree._cut(parent_);
      RestructurableNodeBinaryTree grandparentTree
	= subtree._cut(grandparent_);	
      RestructurableNodeBinaryTree leftTree, rightTree, centerTree;
	
      //re-link the subtree
      if (grandchildTree.root()==center){
	centerTree = grandchildTree;
	if (parentTree.root()==right){
	  rightTree = parentTree;
	  leftTree = grandparentTree;
	}
	else{
	  rightTree = grandparentTree;
	  leftTree = parentTree;
	}
      }
      else{
	centerTree = parentTree;
	if (grandchildTree.root()==right){
	  rightTree = grandchildTree;
	  leftTree = grandparentTree;
	}
	else{
	  rightTree = grandparentTree;
	  leftTree = grandchildTree;
	}
      }

      // retrieve the uninvolved subtrees and reattach them
      // to the involved subtree
      leftTree._replaceSubtree(leftTree.leftChild(leftTree.root()),
			       (BinaryTree)zero.element());
      leftTree._replaceSubtree(leftTree.rightChild(leftTree.root()),
			       (BinaryTree)two.element());
	
      rightTree._replaceSubtree(rightTree.leftChild(rightTree.root()),
				(BinaryTree)four.element());
      rightTree._replaceSubtree(rightTree.rightChild(rightTree.root()),
				(BinaryTree)six.element());	  
	
      Position root = centerTree.root();

	
      centerTree._replaceSubtree(centerTree.leftChild(root), leftTree);
      centerTree._replaceSubtree(centerTree.rightChild(root), rightTree);
	
      // reattach the rotated subtree to the rest of the tree
      if ( gparentIsRoot ){
	_link(root(), centerTree);
      }
      else{
	if (gparentIsRightChild) {
	  _link(rightChild(ggparent), centerTree);
	}
	else {
	  _link(leftChild(ggparent), centerTree);
	}
      }
	
      restructuring_ = false;

      return root;
    }
    
    
    /**
     * Cut off all uninvolved subtrees before rotating, and store the
     * subtrees in the respective leaves left behind by the cutting.
     */
    private RestructurableNodeBinaryTree pruneSubtree() {
      RestructurableNodeBinaryTree temp1 = _cut(leftChild(grandchild_));
      this.replaceElement(leftChild(grandchild_), temp1);
	
      RestructurableNodeBinaryTree temp2 = _cut(rightChild(grandchild_));
      this.replaceElement(rightChild(grandchild_), temp2);
	
      RestructurableNodeBinaryTree temp3;
	
      if (grandchild_== rightChild(parent_)){
	temp3 = _cut(leftChild(parent_));
	this.replaceElement(leftChild(parent_), temp3);    
      }
      else{
	temp3 = _cut(rightChild(parent_));
	this.replaceElement(rightChild(parent_), temp3); 
      }
	
      RestructurableNodeBinaryTree temp4;
	
      if (parent_ == rightChild(grandparent_)){
	temp4 = _cut(leftChild(grandparent_));
	this.replaceElement(leftChild(grandparent_), temp4); 
      }
      else{
	temp4 = _cut(rightChild(grandparent_));
	this.replaceElement(rightChild(grandparent_), temp4); 
      }
	
      RestructurableNodeBinaryTree toret = _cut(grandparent_);
      toret._size = 7;   //always true at this point, and necessary for IOI
                         // to function properly
	
      return toret;
    }
    

    /**
     * Returns a new <code>RestructurableNodeBinaryTree.</code>
     * @return a RestructurableNodeBinaryTree
     */
    public Container newContainer() {
      return new RestructurableNodeBinaryTree();
    }

    
    /**
     * O(1)
     * modified from the code in NodeBinaryTree to function in O(1)
     * (includes removing container modification and not checking for
     * container)
     */
    private RestructurableNodeBinaryTree _cut (Position rootOfSubtree) {
      // cutting means replacing the subtree with a leaf (i.e., with a newly
      // constructed tree)
      RestructurableNodeBinaryTree nc
	= (RestructurableNodeBinaryTree)newContainer();
      return (RestructurableNodeBinaryTree)(_replaceSubtree(rootOfSubtree,nc));
    }


    /**
     * O(1)
     * modified from the code in NodeBinaryTree to function in O(1)
     * (includes removing container modification and not checking for
     * container)
     */
    private void _link (Position mustBeExternal, BinaryTree newSubtree) {
      NBTNode x = checkPosition (mustBeExternal);
      if (isInternal(x))
	throw new InvalidAccessorException
	  ("You can't link at an internal node");
      _replaceSubtree (mustBeExternal, newSubtree);
    }


    /** 
     * O(1)
     * modified from the code in NodeBinaryTree to function in O(1)
     * (includes removing container modification and not checking for
     * container)
     */
    private RestructurableNodeBinaryTree _replaceSubtree
      (Position subtreeRoot, BinaryTree newSubtree) {

      if ( ! (newSubtree instanceof NodeBinaryTree) )
	throw new InvalidContainerException("incompatible type of tree");
      RestructurableNodeBinaryTree toSwapIn
	= (RestructurableNodeBinaryTree) newSubtree;

      // get the roots of the subtrees to be swapped
      NBTNode oldSubtreeRoot = checkPosition (subtreeRoot);
      NBTNode newSubtreeRoot = (NBTNode) toSwapIn.root();

      oldSubtreeRoot.replaceSelf (newSubtreeRoot);

      // make a new tree out of the nodes swapped out; the constructor
      // makes a new tree wrapper pointing to oldSubtreeRoot
      // and forces oldSubtreeRoot to point up to its new container
      RestructurableNodeBinaryTree toReturn
	= new RestructurableNodeBinaryTree(oldSubtreeRoot);

      toReturn.restructuring_ = true;//it must be restructuring, because
      //that's the only thing this method can be used for

      return toReturn;
    }

 
    /**
     * We don't check container if the position is in the middle
     * of a restructuring operation -- otherwise this method is
     * the same as the one it overrides.
     */
    protected NBTNode checkPosition (Accessor a) throws
    InvalidAccessorException {
//       if (a==null)
// 	throw new InvalidAccessorException("null position");

//       if (!(a instanceof NBTNode))
// 	throw new InvalidAccessorException("position of wrong class: "
// 					   + a.getClass());

//       NBTNode n = (NBTNode) a;

//       if ((!restructuring_) && (!(this.contains(n)))) {
// 	throw new InvalidAccessorException
// 	  ("A different container holds this NBTNode!");
//       }
//       return n;
      return (NBTNode) a;
    }
    
  } // end of RestructurableBinaryTree class def

} // end of RedBlackTree class def
