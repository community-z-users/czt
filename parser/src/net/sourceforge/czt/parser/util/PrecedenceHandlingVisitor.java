/*
Copyright (C) 2003, 2004 Tim Miller, Petra Malik
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.util;

import java.util.Iterator;
import java.util.List;
import java.util.Stack;
import java.util.ArrayList;
import java.util.StringTokenizer;
import java.lang.reflect.*;

import java_cup.runtime.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.util.CztException;

/**
 * A PrecedenceHandler re-arranges infix operator expressions
 * so that applications and references to operators of higher precedence
 * are further down in the AST.
 */
public class PrecedenceHandlingVisitor
  implements TermVisitor,
	     ZSectVisitor,
	     ParentVisitor,
	     RefExprVisitor,
	     ApplExprVisitor
{
  /** no precedence given */
  public static final int NO_PREC = -1;

  /** The token for an argument in an operator name */
  public final static String ARG_TOK = "_";

  /** The operator table used to determine the precedence of operators */
  protected OpTable table_;

  /** A ZFactory */
  protected ZFactory zFactory_ = new ZFactoryImpl();

  /** The parents of the terms being analysed */
  protected List parent_ = new ArrayList();

  /**
   * Construct an instance of this handler with a specified
   * operator table
   */
  public PrecedenceHandlingVisitor(OpTable table)
  {
    table_ = table;
  }

  /**
   * Visits all of its children
   */
  public Object visitTerm(Term term)
  {
    Object [] children = term.getChildren();

    for (int i = 0; i < children.length; i++) {
      Object child = children[i];

      //call this method recursively on each child
      if (child instanceof Term) {
	Object visited = ((Term) child).accept(this);
	if (visited != null && visited != child) {
	  reflectiveSwap(child, visited, term, -1);
	}
      }
      else if (child instanceof List) {
	List list = (List) child;
	for (int j = 0; j < list.size(); j++) {
	  Object next = list.get(j);

	  if (next instanceof Term) {
	    Object visited = ((Term) next).accept(this);
	    if (visited != null && visited != next) {
	      reflectiveSwap(child, visited, term, j);
	    }
	  }
	}
      }
    }    
    return null;
  }

  /**
   * We must visit a ZSect in order to set the current section in the
   * operator table
   */
  public Object visitZSect(ZSect zSect)
  {
    String name = zSect.getName();
    assert table_.getSection().equals(name);
    visitTerm(zSect);
    return null;
  }

  /**
   * We must visit a ZSect in order to set the parents in the operator
   * table
   */
  public Object visitParent(Parent parent)
  {
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    visitTerm(refExpr);

    if (WrappedExpr.isValidWrappedExpr(refExpr)) {
      return reorder(new WrappedExpr(refExpr));
    }
    return refExpr;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    visitTerm(applExpr);

    if (WrappedExpr.isValidWrappedExpr(applExpr)) {
      return reorder(new WrappedExpr(applExpr));
    }
    return applExpr;
  }

  protected Expr reorder(WrappedExpr wExpr)
  {
    //if we need to reorder wExpr and its subchild
    if (needsReordering(wExpr)) {

      //we know that the first element of the tuple can be a WrappedExpr,
      //so this should always be safe
      WrappedExpr wChild = new WrappedExpr(wExpr.getList().get(0));

      //create the new parent
      RefName childName = wChild.getRefName();
      Expr newParent = null;
      if (wChild.getExpr() instanceof ApplExpr) {
	RefExpr refExpr = zFactory_.createRefExpr(childName,
						  new ArrayList(),
						  Boolean.FALSE);
	TupleExpr tupleExpr = zFactory_.createTupleExpr();

	newParent = zFactory_.createApplExpr(refExpr,
					     tupleExpr,
					     Boolean.TRUE);
      }
      else {
	newParent = zFactory_.createRefExpr(childName,
					    new ArrayList(),
					    Boolean.TRUE);
      }

      //create the new child
      RefName parentName = wExpr.getRefName();
      Expr newChild = null;
      if (wExpr.getExpr() instanceof ApplExpr) {
	RefExpr refExpr = zFactory_.createRefExpr(parentName,
						  new ArrayList(),
						  Boolean.FALSE);
	TupleExpr tupleExpr = zFactory_.createTupleExpr();

	newChild = zFactory_.createApplExpr(refExpr,
					    tupleExpr,
					    Boolean.TRUE);
      }
      else {
	newChild = zFactory_.createRefExpr(parentName,
					   new ArrayList(),
					   Boolean.TRUE);
      }

      //the next block creates the new parent and child. This is 
      //terribly messy
      WrappedExpr wNewParent = new WrappedExpr(newParent);
      WrappedExpr wNewChild = new WrappedExpr(newChild);

      //the new child keeps the last term in the old child's list and adds it
      //to the front of its list
      wNewChild.getList().add(wChild.getList().get(wChild.getList().size() - 1));

      //get all but the first element of the old parent list and add to
      //the new child
      List fromParentList =
	new ArrayList(wExpr.getList().subList(1, wExpr.getList().size()));
      wNewChild.getList().addAll(fromParentList);      

      //the new parent keeps the front of old childs list
      wNewParent.getList().addAll(wChild.getList().subList(0, wChild.getList().size() - 1));

      //add the new child expression to the end of new parent list
      wNewParent.getList().add(wNewChild.getExpr());

      //recursively visit the parent to reorder ithe new child
      wNewParent.getExpr().accept(this);

      return wNewParent.getExpr();
    }
    return wExpr.getExpr();
  }

  /**
   * Returns true if an only if a specified expression contains a
   * a nested <code>ApplExpr</code> or <code>RefExpr</code>
   * without parenthesise (no <code>ParenAnn</code> annotation) and an
   * infix application or reference that has a lower precedence then it
   */
  protected boolean needsReordering(WrappedExpr wrappedExpr)
  {
    //if the list does not have an ApplExpr or RefExpr in its
    //first position, then we do not have a nested application/reference
    if (wrappedExpr.getList().size() < 2 ||
        (!(wrappedExpr.getList().get(0) instanceof ApplExpr) &&
         !(wrappedExpr.getList().get(0) instanceof RefExpr))) {
      return false;
    }

    //if the nested expr is not a valid WrappedExpr
    WrappedExpr nestedExpr = null;
    if (WrappedExpr.isValidWrappedExpr(wrappedExpr.getList().get(0))) {
      nestedExpr = new WrappedExpr(wrappedExpr.getList().get(0));
    }
    else {
      return false;
    }

    //if the nested Expr has parenthesise then no reordering is required
    if (hasParenAnn(nestedExpr.getExpr())) {
      return false;
    }

    //if the the nested expression is not mixfix
    if (nestedExpr.getMixfix().equals(Boolean.FALSE)) {
      return false;
    }

    //get the precedences of the two expressions
    int prec = getPrec(wrappedExpr.getRefName());
    int nestedPrec = getPrec(nestedExpr.getRefName());

    //if the precedence of refName is lower than the precedence of
    //nestedRefExpr, or they are not infix operators (no precedence
    //info) then no reordering is required
    if (prec < nestedPrec || prec == NO_PREC || nestedPrec == NO_PREC) {
      return false;
    }

    //get the associativities of the two expressions
    Assoc assoc = getAssoc(wrappedExpr.getRefName());
    Assoc nestedAssoc = getAssoc(nestedExpr.getRefName());

    //if the precedences are the same, but the associativity of
    //refExpr is left, then no reordering is required
    if (prec == nestedPrec && assoc == Assoc.Left) {
      return false;
    }

    //if we get to here, then reordering is required
    return true;
  }

  private RefExpr getRefExpr(Expr expr)
  {
    RefExpr result = null;

    if (expr instanceof ApplExpr) {
      ApplExpr applExpr = (ApplExpr) expr;
      if (applExpr.getLeftExpr() instanceof RefExpr) {
        result = (RefExpr) applExpr.getLeftExpr();
      }
    }
    else if (expr instanceof RefExpr) {

    }
    return result;
  }

  //returns true if and only if the specified TermA has a
  //ParenAnn in its annotations
  private boolean hasParenAnn(TermA termA)
  {
    //get the list of annotations
    List anns = termA.getAnns();

    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      //if the next annotation is a ParenAnn
      if (iter.next() instanceof ParenAnn) {
	return true;
      }
    }
    return false;
  }

  //returns the precedence of the name in a RefExpr
  private int getPrec(RefName refName)
  {
    String first = getFirstInfixName(refName);

    int prec = NO_PREC;
    if (first != null) {
      Integer p = table_.getPrec(first);
      if (p != null) {
        prec = p.intValue();
      }
    }
    return prec;
  }

  //returns the associativity of the name in a RefExpr
  private Assoc getAssoc(RefName refName)
  {
    String first = getFirstInfixName(refName);

    Assoc assoc = null;
    if (first != null) {
      assoc = table_.getAssoc(first);
    }
    return assoc;
  }

  private String getName(RefName refName)
  {  
    return refName.getWord();
  }

  private String getFirstInfixName(RefName refName)
  {
    String result = null;
    String name = getName(refName);

    //if the first token is not "_", return null
    StringTokenizer st = new StringTokenizer(name);
    if (st.hasMoreTokens()) {
      String first = st.nextToken();
      if (!first.equals(ARG_TOK)) {
	result = null;
      }
      else {
	if (st.hasMoreTokens()) {
	  //if the second token is a "_", return null
	  String second = st.nextToken();
	  if (second.equals(ARG_TOK)) {
	    result = null;
	  }
	  else {
	    result = second;
	  }
	}
      }
    }
    else {
      result = null;
    }
    return result;
  }

  //use reflection to find the "set" method on the parent, and update
  //the value using this
  private void reflectiveSwap(Object oldObj,
			      Object newObj,
			      Object parent,
			      int position)
  {
    Class c = parent.getClass();
    Method [] methods = c.getMethods();

    for (int i = 0; i < methods.length; i++) {
      Method method = methods[i];

      //find the correct object
      if (method.getName().startsWith("get")) {
	Object result = null;
	try {
	  result = method.invoke(parent, new Object [] {});
	} catch (Exception e) {
	  //do nothing
	} finally {
	  //if the result matches the object to be replaced, we have
	  //found the "get" method for this object
	  if (result == oldObj) {

	    if (result instanceof List) {

	      List list = (List) result;
	      String name = method.getName();

	      //update the value if this is the correct method
	      list.set(position, newObj);
	    }
	    else {

	      //get the name of the corresponding"get" method
	      StringBuffer name = new StringBuffer(method.getName());
	      
	      //turn it into a "set" method
	      name.setCharAt(0, 's');
	      
	      //get the "set" method
	      Method setMethod = null;
	      for (int j = 0; j < methods.length; j++) {
		if (name.toString().equals(methods[j].getName())) {
		  setMethod = methods[j];
		  break;
		}
	      }
	      
	      //call the set method with the new object
	      if (setMethod != null) {
		try {
		  Object [] args = new Object [] {newObj};
		  setMethod.invoke(parent, args);
		} catch (Exception e) {
		  System.err.println("Error updating precedence");
		  e.printStackTrace();
		}
	      }
	    }
	    return;
	  }
	}
      }
    }
  }
}

//This class is used to wrap ApplExpr and RefExpr objects that are
//used as function and generic references respectively. This simplies
//the precedence handling by removing typecasting problems etc
class WrappedExpr
{
  private ZFactory zFactory_ = new ZFactoryImpl();

  private ApplExpr applExpr_;
  private RefExpr refExpr_;

  public WrappedExpr(Object o)
  {
    if (o == null) {
      throw new NullPointerException();
    }

    if (o instanceof ApplExpr) {
      applExpr_ = (ApplExpr) o;

      if (! (applExpr_.getRightExpr() instanceof TupleExpr)) {
        List list = new ArrayList();
        list.add(applExpr_.getRightExpr());
        TupleExpr te = zFactory_.createTupleExpr(list);
        applExpr_.setRightExpr(te);
      }
      
      refExpr_ = null;
    }
    else if (o instanceof RefExpr) {
      refExpr_ = (RefExpr) o;
      applExpr_ = null;
    }
  }
  
  //return true if and only if the specified object is either
  //and ApplExpr or RefExpr used as a function or generic
  //reference respectively
  public static boolean isValidWrappedExpr(Object o)
  {
    boolean result = false;
    
    if (o instanceof ApplExpr) {
      ApplExpr applExpr = (ApplExpr) o;
      Expr leftExpr = applExpr.getLeftExpr();
      Expr rightExpr = applExpr.getRightExpr();
      if (leftExpr instanceof RefExpr &&
	  applExpr.getMixfix().equals(Boolean.TRUE)) {
	result = true;
      }
    }
    else if (o instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) o;
      if (refExpr.getExpr().size() > 1 &&
	  refExpr.getMixfix().equals(Boolean.TRUE)) {
	result = true;
      }
    }
    return result;
  }

  public Expr getExpr()
  {
    Expr result = null;

    if (refExpr_ != null) {
      result = refExpr_;
    }
    else {
      if (applExpr_.getRightExpr() instanceof TupleExpr &&
         ((TupleExpr) applExpr_.getRightExpr()).getExpr().size() == 1) {

         Expr newRightExpr = 
           (Expr) ((TupleExpr) applExpr_.getRightExpr()).getExpr().get(0);
         applExpr_.setRightExpr(newRightExpr);
      }
      result = applExpr_;
    }
    return result;
  }

  public void setRefName(RefName refName)
  {
    if (refExpr_ != null) {
      refExpr_.setRefName(refName);
    }
    else {
      ((RefExpr) applExpr_.getLeftExpr()).setRefName(refName);
    }
  }

  public RefName getRefName()
  {
    RefName result = null;

    if (refExpr_ != null) {
      result = refExpr_.getRefName();
    }
    else {
      result = ((RefExpr) applExpr_.getLeftExpr()).getRefName();
    }
    return result;
  }

  public List getList()
  {
    List result = null;

    if (refExpr_ != null) {
      result = refExpr_.getExpr();
    }
    else {
      result = ((TupleExpr) applExpr_.getRightExpr()).getExpr();
    }
    return result;
  }

  public Boolean getMixfix()
  {
    Boolean result = null;

    if (refExpr_ != null) {
      result = refExpr_.getMixfix();
    }
    else {
      result = applExpr_.getMixfix();
    }
    return result;
  }
}
