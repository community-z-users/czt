/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.rules;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * Unification of ASTs.
 *
 * @author Petra Malik
 */
public class Unification
{
  private UnificationException cause_ = null;
  private boolean provideCause_ = true;
  private Set<Binding> bindings_;

  public static boolean unify(Object o1, Object o2, Set<Binding> bindings)
  {
    Unification unifier = new Unification(bindings);
    return unifier.unify(o1, o2);
  }

  public Unification(Set<Binding> bindings)
  {
    bindings_ = bindings;
  }

  public UnificationException getCause()
  {
    return cause_;
  }

  public void provideCause(boolean value)
  {
    provideCause_ = value;
  }

  public boolean unify(Object o1, Object o2)
  {
    if (o1 == null && o2 == null) {
      return true;
    }
    if (o1 != null && o2 != null) {
      if (o1 instanceof Term && o2 instanceof Term) {
        return unify((Term) o1, (Term) o2);
      }
      if (! o1.equals(o2)) {
        notEqualObjectsFailure(o1, o2);
        return false;
      }
      return true;
    }
    notTermsFailure(o1, o2);
    return false;
  }

  /**
   * Unifies two terms (no occur check).
   *
   * @param term1 the first term.
   * @param term2 the second term.
   * @return <code>true</code> if both term unify,
   *         <code>false</code> otherwise.
   */
  public boolean unify(Term term1, Term term2)
  {
    if (term1 == term2) {
      return true;
    }
    if (term1 instanceof Joker) {
      return handleJoker((Joker) term1, term2);
    }
    if (term2 instanceof Joker) {
      return handleJoker((Joker) term2, term1);
    }
    if (term1.getClass() != term2.getClass()) {
      notSameClassesFailure(term1, term2);
      return false;
    }
    GetChildren visitor = new GetChildren();
    Object[] args1 = term1.accept(visitor);
    Object[] args2 = term2.accept(visitor);
    if (args1.length == args2.length) {
      for (int i = 0; i < args1.length; i++) {
        if (! unify(args1[i], args2[i])) {
          childrenFailure(term1, term2);
          return false;
        }
      }
    }
    else {
      numChildrenFailure(term1, term2);
      return false;
    }
    return true;
  }

  private boolean handleJoker(Joker joker, Term term)
  {
    Term boundTo = joker.boundTo();
    if (boundTo != null && ! (boundTo instanceof List)) {
      return unify(boundTo, term);
    }
    try {
      bindings_.add(joker.bind(term));
      return true;
    }
    catch (IllegalArgumentException e) {
      jokerBindingFailure(joker, term, e);
      return false;
    }
  }

  private void notTermsFailure(Object left, Object right)
  {
    if (provideCause_) {
      String message = "Objects are not terms.";
      cause_ = new UnificationException(left, right, message, cause_);
    }
  }

  private void notSameClassesFailure(Object left, Object right)
  {
    if (provideCause_) {
      String message = "Terms are not of the same type.";
      cause_ = new UnificationException(left, right, message, cause_);
    }
  }

  private void notEqualObjectsFailure(Object left, Object right)
  {
    if (provideCause_) {
      String message = "Objects are not equal.";
      cause_ = new UnificationException(left, right, message, cause_);
    }
  }

  private void jokerBindingFailure(Object left, Object right,
                                          Throwable cause)
  {
    if (provideCause_) {
      String message = "Term cannot be bound to joker.";
      cause_ = new UnificationException(left, right, message, cause_);
    }
  }

  private void childrenFailure(Object left, Object right)
  {
    if (provideCause_) {
      String message = "Children don't match.";
      cause_ = new UnificationException(left, right, message, cause_);
    }
  }

  private void numChildrenFailure(Object left, Object right)
  {
    if (provideCause_) {
      String message = "Different number of children.";
      cause_ = new UnificationException(left, right, message, cause_);
    }
  }

  public static class UnificationException
    extends Exception
  {
    private String reason_;
    private Object left_;
    private Object right_;
    
    public UnificationException(Object left, Object right, String reason)
    {
      reason_ = reason;
      left_ = left;
      right_ = right;
    }

    public UnificationException(Object left, Object right,
                                String reason,
                                Throwable cause)
    {
      super(cause);
      reason_ = reason;
      left_ = left;
      right_ = right;
    }

    public String getMessage()
    {
      if (left_ instanceof Term && right_ instanceof Term) {
        return "Cannot unify " + TermToString.apply((Term) left_) + " and "
          + TermToString.apply((Term) right_) + ": " + reason_
          + "\ncaused by: " + getCause();
      }
      return "Cannot unify " + left_ + " and " + right_ + ": " + reason_
        + "\ncaused by: " + getCause();
    }
  }

  public static class GetChildren
    implements RefExprVisitor<Object[]>,
               TermVisitor<Object[]>,
               ZRefNameVisitor<Object[]>
  {
    /**
     * @czt.todo Fix this!
     */
    public Object[] visitRefExpr(RefExpr refExpr)
    {
      if (refExpr.getMixfix()) {
        return refExpr.getChildren();
      }
      // Ignore type expressions when mixfix is false because
      // expressions in sequents maybe typechecked while expressions
      // in rules are not so that they may be missing type expressions.
      // This is a hack!
      return new Object[] { refExpr.getRefName() };
    }

    public Object[] visitTerm(Term term)
    {
      return term.getChildren();
    }

    public Object[] visitZRefName(ZRefName zRefName)
    {
      return new Object[] { zRefName.getWord(), zRefName.getStroke() };
    }
  }

  protected static interface Wrapper
  {
    Object getContent();
    Object[] getChildren();
  }


  /**
   * Changes the internal ZExprList when getChildren()
   * is called!
   */
  protected static class ZExprListWrapper
    implements Wrapper
  {
    private ZExprList zExprList_;

    public ZExprListWrapper(ZExprList zExprList)
    {
      zExprList_ = (ZExprList) zExprList.create(zExprList.getChildren());
    }

    public Object getContent()
    {
      return zExprList_;
    }

    public Object[] getChildren()
    {
      if (zExprList_.isEmpty()) {
        return new Object[] { null, null };
      }
      return new Object[] { zExprList_.remove(0), this };
    }
  }

  /*
  protected static class HeadExprListWrapper
    implements Wrapper
  {
    private HeadExprList headExprList_;

    public HeadExprListWrapper(HeadExprList headExprList)
    {
      headExprList_ =
        (HeadExprList) headExprList.create(headExprList.getChildren());
    }

    public Object getContent()
    {
      return headExprList_;
    }

    public Object[] getChildren()
    {
      if (headExprList.getZExprList().isEmpty()) {
        return new Object[] { headExprList.get
      }
    }
  }
  */
}
