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
import java.util.Map;
import java.util.StringTokenizer;
import java.lang.reflect.*;

import java_cup.runtime.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * A PrecedenceHandler re-arranges infix operator expressions
 * so that applications and references to operators of higher precedence
 * are further down in the AST.
 * This is described in note 3 of section 8.3 of the Z standard.
 */
public class PrecedenceHandlingVisitor
  implements TermVisitor,
             ZSectVisitor,
             RefExprVisitor,
             ApplExprVisitor,
	     ProdExprVisitor
{
  //the precedence of a cross product
  protected static Integer PRODEXPR_PRECEDENCE = new Integer(8);

  private Map tables_;

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
  public PrecedenceHandlingVisitor(Map table)
  {
    tables_ = table;
  }

  /**
   * Visits all of its children.
   */
  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  /**
   * We must visit a ZSect in order to set the current section in the
   * operator table.
   */
  public Object visitZSect(ZSect zSect)
  {
    String name = zSect.getName();
    table_ = (OpTable) tables_.get(name);
    return visitTerm(zSect);
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    Object o = visitTerm(refExpr);

    if (WrappedExpr.isValidWrappedExpr(o)) {
      return reorder(new WrappedExpr(o));
    }
    return o;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    Object o = visitTerm(applExpr);

    if (WrappedExpr.isValidWrappedExpr(o)) {
      return reorder(new WrappedExpr(o));
    }
    return o;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    Object o = visitTerm(prodExpr);

    if (WrappedExpr.isValidWrappedExpr(o)) {
      return reorder(new WrappedExpr(o));
    }
    return o;
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
      else if (wChild.getExpr() instanceof ProdExpr) {
	newParent = zFactory_.createProdExpr();
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
      else if (wExpr.getExpr() instanceof ProdExpr) {
	newChild = zFactory_.createProdExpr();
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

    //if the list does not have an ApplExpr, RefExpr, or ProdExpr in its
    //first position, then we do not have a nested application/reference
    if (wrappedExprList.size() < 2 ||
        (!(firstElem instanceof ApplExpr) &&
         !(firstElem instanceof RefExpr) &&
	 !(firstElem instanceof ProdExpr))) {
      System.err.println("return 1");
      return false;
    }

    //if the nested expr is not a valid WrappedExpr
    WrappedExpr nestedExpr = null;
    if (WrappedExpr.isValidWrappedExpr(firstElem)) {
      nestedExpr = new WrappedExpr(firstElem);
    }
    else {
      System.err.println("return 2");
      System.err.println("\t type = " + firstElem.getClass().getName());
      return false;
    }

    //if the nested Expr has parenthesise then no reordering is required
    if (hasParenAnn(nestedExpr.getExpr())) {
      System.err.println("return 3");
      return false;
    }

    //if the the nested expression is not mixfix
    if (nestedExpr.getMixfix().equals(Boolean.FALSE)) {
      System.err.println("return 4");
      return false;
    }

    //get the precedences of the two expressions
    Integer prec = getPrec(wrappedExpr);
    Integer nestedPrec = getPrec(nestedExpr);

    //if the precedence of refName is lower than the precedence of
    //nestedRefExpr, or they are not infix operators (no precedence
    //info) then no reordering is required
    if (prec == null || nestedPrec == null || prec.compareTo(nestedPrec) < 0) {
      System.err.println("return 5");
      return false;
    }

    //get the associativities of the two expressions
    Assoc assoc = getAssoc(wrappedExpr);
    Assoc nestedAssoc = getAssoc(nestedExpr);

    //if the precedences are the same, but the associativity of
    //refExpr is left, then no reordering is required
    if (prec.compareTo(nestedPrec) == 0 && assoc == Assoc.Left) {
      System.err.println("return 6");
      return false;
    }

    //if we get to here, then reordering is required
    System.err.println("return true");
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
   * Returns the precedence of the name in a wrapped expr
   * or <code>null</code> if no precedence is given.
   */
  private Integer getPrec(WrappedExpr wrappedExpr)
  {
    Integer result = null;
    if (wrappedExpr.getExpr() instanceof ProdExpr) {
      result = PRODEXPR_PRECEDENCE;
    }
    else {
      RefName refName = wrappedExpr.getRefName();
      String first = getFirstInfixName(refName);
      if (first != null) {
	result = table_.getPrec(first);
      }
    }
    return result;
  }

  /**
   * Returns the associativity of the name in a RefExpr.
   */
  private Assoc getAssoc(WrappedExpr wrappedExpr)
  {
    Assoc assoc = null;
    if (wrappedExpr.getExpr() instanceof ProdExpr) {
      assoc = Assoc.Right;
    }
    else {
      String first = getFirstInfixName(wrappedExpr.getRefName());
      if (first != null) {
	assoc = table_.getAssoc(first);
      }
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
}

/**
 * This class is used to wrap ApplExpr, RefExpr, a,d ProdExpr objects
 * that are used as function and generic references, and cross
 * products respectively. This simplies the precedence handling by
 * removing typecasting problems etc.
 */
class WrappedExpr
{
  private ZFactory zFactory_ = new ZFactoryImpl();

  private ApplExpr applExpr_ = null;
  private RefExpr refExpr_ = null;
  private ProdExpr prodExpr_ = null;

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
    }
    else if (o instanceof RefExpr) {
      refExpr_ = (RefExpr) o;
    }
    else if (o instanceof ProdExpr) {
      prodExpr_ = (ProdExpr) o;
    }
  }

  /**
   * Returns true if and only if the specified object is either
   * and ApplExpr or RefExpr used as a function or generic
   * reference respectively, or a cross product
   */
  public static boolean isValidWrappedExpr(Object o)
  {
    if (o instanceof ApplExpr) {
      return isValidWrappedExpr((ApplExpr) o);
    }
    else if (o instanceof RefExpr) {
      return isValidWrappedExpr((RefExpr) o);
    }
    else if (o instanceof ProdExpr) {
      return true;
    }
    return false;
  }

  public static boolean isValidWrappedExpr(ApplExpr applExpr)
  {
    Expr leftExpr = applExpr.getLeftExpr();
    Expr rightExpr = applExpr.getRightExpr();
    boolean result = leftExpr instanceof RefExpr &&
      applExpr.getMixfix().equals(Boolean.TRUE);
    return result;
  }

  public static boolean isValidWrappedExpr(RefExpr refExpr)
  {
    boolean result = refExpr.getExpr().size() > 1 &&
      refExpr.getMixfix().equals(Boolean.TRUE);
    return result;
  }

  public Expr getExpr()
  {
    Expr result = null;

    if (refExpr_ != null) {
      result = refExpr_;
    }
    else if (prodExpr_ != null) {
      result = prodExpr_;
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

  public RefName getRefName()
  {
    RefName result = null;

    if (refExpr_ != null) {
      result = refExpr_.getRefName();
    }
    else if (prodExpr_ != null) {
      result = null;
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
    else if (prodExpr_ != null) {
      result = prodExpr_.getExpr();
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
    else if (prodExpr_ != null) {
      result = Boolean.TRUE;
    }
    else {
      result = applExpr_.getMixfix();
    }
    return result;
  }
}
