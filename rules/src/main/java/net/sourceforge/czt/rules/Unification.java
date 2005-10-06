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
    Object[] args1 = term1.getChildren();
    Object[] args2 = term2.getChildren();
    assert args1.length == args2.length;
    for (int i = 0; i < args1.length; i++) {
      if (! unify(args1[i], args2[i])) {
        childrenFailure(term1, term2);
        return false;
      }
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
      return "Cannot unify " + left_ + " and " + right_ + ": " + reason_
        + "\ncaused by: " + getCause();
    }
  }
}
