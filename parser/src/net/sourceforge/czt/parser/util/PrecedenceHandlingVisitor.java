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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;
import java.lang.reflect.*;

import java_cup.runtime.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * A PrecedenceHandler re-arranges infix operator expressions
 * so that applications and references to operators of higher precedence
 * are further down in the AST.
 */
public class PrecedenceHandlingVisitor
  implements TermVisitor,
             ZSectVisitor,
             RefExprVisitor,
             ApplExprVisitor
{
  /** The operator table used to determine the precedence of operators. */
  protected OpTable table_;

  /** A ZFactory. */
  protected ZFactory zFactory_ = new ZFactoryImpl();

  /** The parents of the terms being analysed. */
  protected List parent_ = new ArrayList();

  /**
   * Constructs an instance of this handler with a specified
   * operator table.
   */
  public PrecedenceHandlingVisitor(OpTable table)
  {
    table_ = table;
  }

  /**
   * Visits all of its children.
   */
  public Object visitTerm(Term term)
  {
    Object [] children = term.getChildren();

    for (int i = 0; i < children.length; i++) {
      Object child = children[i];

      //call this method recursively on each child
      if (child instanceof List) {
        List list = (List) child;
        int count = 0;
        for (Iterator iter = list.iterator(); iter.hasNext();) {
          Object next = iter.next();
          if (next instanceof Term) {
            Object visited = ((Term) next).accept(this);
            if (visited != null && visited != next) {
              reflectiveSwap(child, visited, term, count);
            }
          }
          count++;
        }
      }
      else if (child instanceof Term) {
        Object visited = ((Term) child).accept(this);
        if (visited != null && visited != child) {
          reflectiveSwap(child, visited, term, -1);
        }
      }
    }
    return null;
  }

  /**
   * We must visit a ZSect in order to set the current section in the
   * operator table.
   */
  public Object visitZSect(ZSect zSect)
  {
    String name = zSect.getName();
    assert table_.getSection().equals(name);
    zSect.getPara().accept(this);
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
        RefExpr refExpr =
          zFactory_.createRefExpr(childName, new ArrayList(), Boolean.FALSE);
        TupleExpr tupleExpr = zFactory_.createTupleExpr();
        newParent =
          zFactory_.createApplExpr(refExpr, tupleExpr, Boolean.TRUE);
      }
      else {
        newParent =
          zFactory_.createRefExpr(childName, new ArrayList(), Boolean.TRUE);
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
      List wChildList = wChild.getList();
      List wNewChildList = wNewChild.getList();
      wNewChildList.add(wChildList.get(wChildList.size() - 1));

      //get all but the first element of the old parent list and add to
      //the new child
      List fromParentList =
        new ArrayList(wExpr.getList().subList(1, wExpr.getList().size()));
      wNewChildList.addAll(fromParentList);
      List wNewParentList = wNewParent.getList();
      //the new parent keeps the front of old childs list
      wNewParentList.addAll(wChildList.subList(0, wChildList.size() - 1));

      //add the new child expression to the end of new parent list
      wNewParentList.add(wNewChild.getExpr());

      //recursively visit the parent to reorder ithe new child
      wNewParent.getExpr().accept(this);

      return wNewParent.getExpr();
    }
    return wExpr.getExpr();
  }

  /**
   * Returns <code>true<code> iff a specified expression contains a
   * a nested <code>ApplExpr</code> or <code>RefExpr</code>
   * without parenthesise (no <code>ParenAnn</code> annotation) and an
   * infix application or reference that has a lower precedence then it.
   */
  protected boolean needsReordering(WrappedExpr wrappedExpr)
  {
    final List wrappedExprList = wrappedExpr.getList();
    final Object firstElem =
      wrappedExprList.size() > 0 ? wrappedExprList.get(0) : null;

    //if the list does not have an ApplExpr or RefExpr in its
    //first position, then we do not have a nested application/reference
    if (wrappedExprList.size() < 2 ||
        (!(firstElem instanceof ApplExpr) &&
         !(firstElem instanceof RefExpr))) {
      return false;
    }

    //if the nested expr is not a valid WrappedExpr
    WrappedExpr nestedExpr = null;
    if (WrappedExpr.isValidWrappedExpr(firstElem)) {
      nestedExpr = new WrappedExpr(firstElem);
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
    Integer prec = getPrec(wrappedExpr.getRefName());
    Integer nestedPrec = getPrec(nestedExpr.getRefName());

    //if the precedence of refName is lower than the precedence of
    //nestedRefExpr, or they are not infix operators (no precedence
    //info) then no reordering is required
    if (prec == null || nestedPrec == null || prec.compareTo(nestedPrec) < 0) {
      return false;
    }

    //get the associativities of the two expressions
    Assoc assoc = getAssoc(wrappedExpr.getRefName());
    Assoc nestedAssoc = getAssoc(nestedExpr.getRefName());

    //if the precedences are the same, but the associativity of
    //refExpr is left, then no reordering is required
    if (prec.compareTo(nestedPrec) == 0 && assoc == Assoc.Left) {
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

  /**
   * Returns the precedence of the name in a RefExpr,
   * or <code>null</code> if no precedence is given.
   */
  private Integer getPrec(RefName refName)
  {
    String first = getFirstInfixName(refName);
    Integer result = null;
    if (first != null) {
      result = table_.getPrec(first);
    }
    return result;
  }

  /**
   * Returns the associativity of the name in a RefExpr.
   */
  private Assoc getAssoc(RefName refName)
  {
    String first = getFirstInfixName(refName);

    Assoc assoc = null;
    if (first != null) {
      assoc = table_.getAssoc(first);
    }
    return assoc;
  }

  private String getFirstInfixName(RefName refName)
  {
    String result = null;
    String name = refName.getWord();

    //if the first token is not "_", return null
    StringTokenizer st = new StringTokenizer(name);
    if (st.hasMoreTokens()) {
      String first = st.nextToken();
      if (!first.equals(ZString.ARG)) {
        result = null;
      }
      else {
        if (st.hasMoreTokens()) {
          //if the second token is a "_", return null
          String second = st.nextToken();
          if (second.equals(ZString.ARG)) {
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

  /**
   * Use reflection to find the "set" method on the parent, and update
   * the value using this.
   */
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
        }
        catch (Exception e) {
          //do nothing
        }
        finally {
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
                }
                catch (Exception e) {
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

/**
 * This class is used to wrap ApplExpr and RefExpr objects that are
 * used as function and generic references respectively. This simplies
 * the precedence handling by removing typecasting problems etc.
 */
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

  /**
   * Returns true if and only if the specified object is either
   * and ApplExpr or RefExpr used as a function or generic
   * reference respectively.
   */
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
