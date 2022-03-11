/*
  Copyright (C) 2003, 2004, 2005 Tim Miller
  Copyright (C) 2003, 2004, 2005, 2006, 2007 Petra Malik
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * A PrecedenceHandler re-arranges infix operator expressions
 * so that applications and references to operators of higher precedence
 * are further down in the AST.
 * This is described in note 3 of section 8.3 of the Z standard.
 */
public class PrecedenceHandlingVisitor
  implements TermVisitor<Term>,
             RefExprVisitor<Term>,
             ApplExprVisitor<Term>,
             ProdExprVisitor<Term>
{
  /** The precedence of a cross product. */
  protected static final BigInteger PRODEXPR_PRECEDENCE =
    BigInteger.valueOf(8);

  /** The operator table used to determine the precedence of operators. */
  protected OpTable table_;

  /** A ZFactory. */
  protected Factory factory_ = new Factory(new ZFactoryImpl());

  /**
   * Constructs an instance of this handler with a specified
   * operator table.
   */
  public PrecedenceHandlingVisitor(OpTable opTable)
  {
    table_ = opTable;
  }

  /**
   * Visits all of its children and copies annotations.
   */
  public Term visitTerm(Term term)
  {
    Term result = VisitorUtils.visitTerm(this, term, true);
    return result;
  }

  private Term handleExpr(Expr expr)
  {
    Term term = visitTerm(expr);
    if (WrappedExpr.isValidWrappedExpr(term)) {
      return reorder(new WrappedExpr(term));
    }
    return term;
  }

  public Term visitRefExpr(RefExpr refExpr)
  {
    return handleExpr(refExpr);
  }

  public Term visitApplExpr(ApplExpr applExpr)
  {
    return handleExpr(applExpr);
  }

  public Term visitProdExpr(ProdExpr prodExpr)
  {
    return handleExpr(prodExpr);
  }

  protected Expr createExpr(WrappedExpr wrappedExpr)
  {
    final Name refName = wrappedExpr.getName();
    final ZExprList zExprList = factory_.createZExprList();
    if (wrappedExpr.getExpr() instanceof ApplExpr) {
      RefExpr refExpr =
        factory_.createRefExpr(refName, zExprList, Boolean.FALSE);
      TupleExpr tupleExpr =
        factory_.createTupleExpr(factory_.createZExprList());
      return factory_.createApplExpr(refExpr, tupleExpr, Boolean.TRUE);
    }
    else if (wrappedExpr.getExpr() instanceof ProdExpr) {
      return factory_.createProdExpr(factory_.createZExprList());
    }
    return factory_.createRefExpr(refName, zExprList,
                                  Boolean.TRUE, Boolean.TRUE);
  }

  protected Expr reorder(WrappedExpr wExpr)
  {
    //if we need to reorder wExpr and its subchild
    if (needsReordering(wExpr)) {
      //we know that the first element of the tuple can be a WrappedExpr,
      //so this should always be safe
      WrappedExpr wChild = new WrappedExpr(wExpr.getList().get(0));

      //create the new parent
      Expr newParent = createExpr(wChild);
      if (hasParenAnn(wExpr.getExpr())) {
        newParent.getAnns().add(factory_.createParenAnn());
      }

      //create the new child
      Expr newChild = createExpr(wExpr);

      //the next block creates the new parent and child. This is
      //terribly messy
      WrappedExpr wNewParent = new WrappedExpr(newParent);
      WrappedExpr wNewChild = new WrappedExpr(newChild);
      //the new child keeps the last term in the old child's list and adds it
      //to the front of its list
      List<Expr> wChildList = wChild.getList();
      List<Expr> wNewChildList = wNewChild.getList();
      wNewChildList.add(wChildList.get(wChildList.size() - 1));

      //get all but the first element of the old parent list and add to
      //the new child
      List<Expr> fromParentList =
        new ArrayList<Expr>(wExpr.getList().subList(1, wExpr.getList().size()));
      wNewChildList.addAll(fromParentList);
      List<Expr> wNewParentList = wNewParent.getList();
      //the new parent keeps the front of old childs list
      wNewParentList.addAll(wChildList.subList(0, wChildList.size() - 1));

      //add the new child expression to the end of new parent list
      wNewParentList.add(wNewChild.getExpr());

      //recursively visit the parent to reorder the new child
      return (Expr) wNewParent.getExpr().accept(this);
    }
    return wExpr.getExpr();
  }

  /**
   * Returns <code>true</code> iff a specified expression contains a
   * a nested <code>ApplExpr</code> or <code>RefExpr</code>
   * without parenthesise (no <code>ParenAnn</code> annotation) and an
   * infix application or reference that has a lower precedence then it.
   */
  protected boolean needsReordering(WrappedExpr wrappedExpr)
  {
    final List<Expr> wrappedExprList = wrappedExpr.getList();
    final Object firstElem =
      wrappedExprList.size() > 0 ? wrappedExprList.get(0) : null;

    //if the list does not have an ApplExpr, RefExpr, or ProdExpr in its
    //first position, then we do not have a nested application/reference
    if (wrappedExprList.size() < 2 ||
        (!(firstElem instanceof ApplExpr) &&
         !(firstElem instanceof RefExpr) &&
         !(firstElem instanceof ProdExpr))) {
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
    BigInteger prec = getPrec(wrappedExpr);
    BigInteger nestedPrec = getPrec(nestedExpr);

    //if the precedence of refName is lower than the precedence of
    //nestedRefExpr, or they are not infix operators (no precedence
    //info) then no reordering is required
    if (prec == null || nestedPrec == null || prec.compareTo(nestedPrec) < 0) {
      return false;
    }

    //get the associativities of the two expressions
    Assoc assoc = getAssoc(wrappedExpr);

    //if the precedences are the same, but the associativity of
    //refExpr is left, then no reordering is required
    if (prec.compareTo(nestedPrec) == 0 && assoc == Assoc.Left) {
      return false;
    }

    //if we get to here, then reordering is required
    return true;
  }

  //returns true if and only if the specified Term has a
  //ParenAnn in its annotations
  private boolean hasParenAnn(Term term)
  {
    return (term.getAnn(ParenAnn.class) != null);
  }

  /**
   * Returns the precedence of the name in a wrapped expr
   * or <code>null</code> if no precedence is given.
   */
  private BigInteger getPrec(WrappedExpr wrappedExpr)
  {
    BigInteger result = null;
    if (wrappedExpr.getExpr() instanceof ProdExpr) {
      result = PRODEXPR_PRECEDENCE;
    }
    else {
      ZName refName = wrappedExpr.getName();
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
      String first = getFirstInfixName(wrappedExpr.getName());
      if (first != null) {
        assoc = table_.getAssoc(first);
      }
    }
    return assoc;
  }

  private String getFirstInfixName(ZName refName)
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
  private Factory factory_ = new Factory(new ZFactoryImpl());

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
        ZExprList zExprList = factory_.createZExprList();
        zExprList.add(applExpr_.getRightExpr());
        TupleExpr te = factory_.createTupleExpr(zExprList);
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
   * Returns <code>true</code> if and only if the specified object is either
   * an ApplExpr or RefExpr used as a function or generic
   * reference respectively, or a cross product.
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
    boolean result = leftExpr instanceof RefExpr &&
      applExpr.getMixfix().equals(Boolean.TRUE);
    return result;
  }

  public static boolean isValidWrappedExpr(RefExpr refExpr)
  {
    boolean result = refExpr.getExprList() instanceof ZExprList &&
      refExpr.getZExprList().size() > 1 &&
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
      final Expr rightExpr = applExpr_.getRightExpr();
      if (rightExpr instanceof TupleExpr) {
        final TupleExpr tupleExpr = (TupleExpr) rightExpr;
        final List<Expr> exprs = tupleExpr.getZExprList();
        if (exprs.size() == 1) {
          final Expr newRightExpr = exprs.get(0);
          applExpr_.setRightExpr(newRightExpr);
        }
      }
      result = applExpr_;
    }
    return result;
  }

  public ZName getName()
  {
    ZName result = null;

    if (refExpr_ != null) {
      result = refExpr_.getZName();
    }
    else if (prodExpr_ != null) {
      result = null;
    }
    else {
      result = ((RefExpr) applExpr_.getLeftExpr()).getZName();
    }
    return result;
  }

  public List<Expr> getList()
  {
    List<Expr> result = null;

    if (refExpr_ != null) {
      result = refExpr_.getZExprList();
    }
    else if (prodExpr_ != null) {
      result = prodExpr_.getZExprList();
    }
    else {
      result = ((TupleExpr) applExpr_.getRightExpr()).getZExprList();
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
