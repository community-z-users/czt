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

package net.sourceforge.czt.zpatt.util;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zpatt.ast.*;

/**
 * A simple deduction implementation.
 *
 * @author Petra Malik
 */
public class DeductionImpl
  implements Deduction
{
  private Rule rule_;
  private PredSequent conclusion_;
  private boolean valid_ = false;
  private Sequent[] children_ = null;
  private Map<Term,Term> bindings_ = new HashMap();

  public DeductionImpl(Rule rule, PredSequent conclusion)
  {
    rule_ = rule;
    conclusion_ = conclusion;
  }

  public String getName()
  {
    return rule_.getName();
  }

  public void next()
  {
    valid_ = false;
  }

  public boolean isValid()
  {
    return valid_;
  }

  public Sequent[] children()
  {
    return children_;
  }

  /**
   * Matches a term which may contain joker agains a term
   * without joker.
   *
   * @param term1 a term that may contain joker.
   * @param term2 a term without joker.
   * @return a list of bindings,
   *         or <code>null</code> if the two terms do not match.
   */
  private boolean match(Term term1, Term term2)
  {
    if (term1 == term2) {
      return true;
    }
    if (term1 instanceof JokerExpr) {
      if (term2 instanceof Expr) {
        JokerExpr joker = (JokerExpr) term1;
        Term boundTo = bindings_.get(joker);
        if (boundTo != null) {
          return boundTo.equals(term2);
        }
        bindings_.put(joker, term2);
        return true;
      }
      else {
        // term2 has wrong type
        return false;
      }
    }
    if (term1 instanceof JokerPred) {
      if (term2 instanceof Pred) {
        JokerPred joker = (JokerPred) term1;
        Term boundTo = (Term) bindings_.get(joker);
        if (boundTo != null) {
          return boundTo.equals(term2);
        }
        bindings_.put(joker, term2);
        return true;
      }
      else {
        // term2 has wrong type
        return false;
      }
    }
    if (term1.getClass() != term2.getClass()) {
      return false;
    }
    Object[] args1 = term1.getChildren();
    Object[] args2 = term2.getChildren();
    for (int i = 0; i < args1.length; i++) {
      if (args1[i] == null && args2[i] != null) {
        return false;
      }
      if (args1[i] != null) {
        if (args1[i] instanceof Term) {
          Term child1 = (Term) args1[i];
          Term child2 = (Term) args2[i];
          if (! match(child1, child2)) {
            return false;
          }
        }
        else if (args1[i] instanceof List) {
          List list1 = (List) args1[i];
          List list2 = (List) args2[i];
          if (! match(list1, list2)) {
            return false;
          }
        }
        else {
          if (! args1[i].equals(args2[i])) {
            return false;
          }
        }
      }
    }
    return true;
  }

  private boolean match(List list1, List list2)
  {
    if (list1.size() != list2.size()) {
      return false;
    }
    for (int i = 0; i < list1.size(); i++) {
      Object o1 = list1.get(i);
      Object o2 = list2.get(i);
      if (o1 instanceof Term && o2 instanceof Term) {
        if (! match((Term) o1, (Term) o2)) {
          return false;
        }
      }
      else {
        if (! o1.equals(o2)) {
          return false;
        }
      }
    }
    return true;
  }
}
