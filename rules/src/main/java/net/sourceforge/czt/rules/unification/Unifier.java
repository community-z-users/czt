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

package net.sourceforge.czt.rules.unification;

import java.util.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.zpatt.ast.Binding;

/**
 * <p>Unification of ASTs.</p>
 *
 * <p>Before unification can be applied, the AST containing jokers
 * need to be transformed into a suitable form so that the joker
 * implement the {@link Joker} interface.  It is assumed that, if a
 * joker gets bound to a term, automatically all jokers of the same
 * type and with the same name get bound to that term.</p>
 *
 * @author Petra Malik
 */
public class Unifier
{
  private UnificationException cause_ = null;
  private boolean provideCause_ = true;
  private Set<Binding> bindings_ = new HashSet<Binding>();

  public Set<Binding> getBindings()
  {
    return bindings_;
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
    Packer packer = new Packer();
    term1 = term1.accept(packer);
    term2 = term2.accept(packer);
    if (term1 == term2) {
      return true;
    }
    if (term1 instanceof Joker) {
      return handleJoker((Joker) term1, term2);
    }
    if (term2 instanceof Joker) {
      return handleJoker((Joker) term2, term1);
    }
    ChildExtractor visitor = new ChildExtractor();
    Object[] args1 = term1.accept(visitor);
    Object[] args2 = term2.accept(visitor);
    if (args1.length == args2.length) {
      for (int i = 0; i < args1.length; i++) {
        if (! unify(args1[i], args2[i])) {
          childrenFailure(term1, term2, i);
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
    if (boundTo != null) {
      return unify(boundTo, term);
    }
    if (term instanceof Wrapper) {
      term = ((Wrapper) term).getContent();
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

  private void childrenFailure(Object left, Object right, int i)
  {
    if (provideCause_) {
      String message = "Children at index " + i + " don't match.";
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
}
