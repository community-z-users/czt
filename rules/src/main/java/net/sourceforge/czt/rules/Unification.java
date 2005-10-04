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

public final class Unification
{
  public static Object o1_;
  public static Object o2_;
  public static String reason_;

  public static boolean unify(Object o1, Object o2, Set<Binding> bindings)
  {
    if (o1 == null && o2 == null) {
      return true;
    }
    if (o1 != null && o2 != null) {
      if (o1 instanceof Term && o2 instanceof Term) {
        return unify((Term) o1, (Term) o2, bindings);
      }
      return o1.equals(o2);
    }
    o1_ = o1;
    o2_ = o2;
    reason_ = "object";
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
  public static boolean unify(Term term1, Term term2, Set<Binding> bindings)
  {
    if (term1 == term2) {
      return true;
    }
    if (term1 instanceof Joker) {
      return handleJoker((Joker) term1, term2, bindings);
    }
    if (term2 instanceof Joker) {
      return handleJoker((Joker) term2, term1, bindings);
    }
    if (term1.getClass() != term2.getClass()) {
      o1_ = term1;
      o2_ = term2;
      reason_ = "not of the same class";
      return false;
    }
    Object[] args1 = term1.getChildren();
    Object[] args2 = term2.getChildren();
    assert args1.length == args2.length;
    for (int i = 0; i < args1.length; i++) {
      if (! unify(args1[i], args2[i], bindings)) {
        return false;
      }
    }
    return true;
  }

  private static boolean handleJoker(Joker joker, Term term,
                                     Set<Binding> bindings)
  {
    Term boundTo = joker.boundTo();
    if (boundTo != null && ! (boundTo instanceof List)) {
      return unify(boundTo, term, bindings);
    }
    try {
      bindings.add(joker.bind(term));
      return true;
    }
    catch (IllegalArgumentException e) {
      o1_ = joker;
      o2_ = term;
      reason_ = "cannot bind to joker";
      return false;
    }
  }
}
