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

package net.sourceforge.czt.jdsl.core.algo.traversals;
import net.sourceforge.czt.jdsl.core.api.*;


/**
  * The EulerTour algorithm is a tree traversal that can be informally 
  * described as a walk around tree T, where we start by going from the
  * root towards its left child, viewing the edges of T as being "walls"
  * that we always keep to our left.
  * <p>
  * Each internal node v of T with c children is seen c+1 times:<br>
  * 1. "on the left" (before the Euler tour of v's left subtree<br>
  * 2. "between children" (between the Euler tours of the subtrees)<br>
  * 3. "on the right" (after the Euler tour of v's right subtree)<br>
  * Each external node of T is seen one time.
  *
  * This algorithm object uses the template method pattern.
  * To do anything useful, at least one of the methods
  * visitFirst(Pos), visitBetweenChildren(Pos), and visitLast(Pos), 
  * and visitExternal(Pos) will need to be redefined in a subclass.
  * 
  * The algorithm can be used multiple times after construction.
  * It is run by a call to the execute(.) method, which takes an
  * InspectableTree as its parameter.  It produces no output except
  * any output you cause it to produce in the redefined methods
  * mentioned above.
  *
 * @author Lucy Perry (lep)
 * @author Mark Handy
  *
  * @version JDSL 2.1.1 
  */

public abstract class EulerTour {
    
    
    /**
     * The tree on which the algorithm executes.
     * It should be passed in via the execute() method
     */
    protected InspectableTree tree_;
    
    
    /**
     * The constructor for the algorithm. 
     * Does nothing, but may be extended to do useful set-up.
     */
    public EulerTour(){
    }
    
    
    
    
    /**
     * This method should be called after construction.
     * It may be used more than once, with different Tree objects.
     * It begins by calling the init() method, to take care of any
     * preprocessing on the Tree, and then executes the recursive tour.
     *
     * @param tree the InspectableTree to tour
     * @throws InvalidContainerException if the Tree is null
     */
    public void execute(InspectableTree tree) throws InvalidContainerException{
	if (tree == null) throw new InvalidContainerException
		("Can't execute Euler Tour on a null tree.");
	tree_ = tree;
	init();
	tourSubtree(tree_.root());
    }
    
    
    /**
     * The meat of the algorithm.
     * This method is called recursively.
     * 
     * @param subtreeRoot subtreeRoot
     */
    private void tourSubtree(Position subtreeRoot){
	if (tree_.isInternal(subtreeRoot)){
	    visitFirstTime(subtreeRoot);
	    PositionIterator offspring = tree_.children(subtreeRoot);
	    Position curChild;
	    while (offspring.hasNext()){
		curChild = offspring.nextPosition();
		tourSubtree(curChild);
		if (offspring.hasNext()){
		    visitBetweenChildren(subtreeRoot);
		}
	    }
	    visitLastTime(subtreeRoot);
	}
	else visitExternal( subtreeRoot );
    }
    
    
    /**
     * Called in execute(.), before algorithm is executed.
     * May be overridden in a subclass, to take care of any setup.
     */
    protected void init() { }
    
    
    /**
     * Called during execution when a node is first visited in the
     * Euler tour. 
     * May be overridden in a subclass.
     */
    protected void visitFirstTime(Position pos) { }
    
    
    /**
     * Called during execution when a node is visited between visits
     * to its children. 
     * May be overridden in a subclass.
     */
    protected void visitBetweenChildren(Position pos) { }
    
    
    /**
     * Called during execution when a node is visted for the last time
     * in the Euler tour. 
     * May be overridden in a subclass.
     */
    protected void visitLastTime(Position pos) { }
    

    /** 
     * Called during execution when an external node is visited during
     * the Euler tour.  An external node (a/k/a leaf) is seen only
     * once; this one visit subsumes the visit from the left, the
     * visit from below, and the visit from the right. The default behavior
     * calls the visitFirstTime and visitLastTime methods.
     */
    protected void visitExternal( Position pos ) { 
        visitFirstTime(pos);
        visitLastTime(pos);
    }


}




    
    
    

