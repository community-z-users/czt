/*
  Copyright (C) 2005 Petra Malik
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
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.zpatt.ast.Binding;

/**
 * <p>Unification of ASTs.</p>
 *
 * <p>The unify methods in this class assume that all the jokers
 * in both ASTs implement the {@link Joker} interface.  They also
 * assume that, if a joker gets bound to a term, automatically all
 * jokers of the same type and with the same name get bound to
 * that term.  The ProverFactory should be used to ensure these
 * properties.</p>
 *
 * @author Petra Malik
 */
public class Unifier
{
  private UnificationException cause_ = null;
  private boolean provideCause_ = true;
  private Set<Binding> bindings_ = new HashSet<Binding>();

  private OccursCheckVisitor occursCheck = new OccursCheckVisitor();

  /** Used for debugging/tracing difficult unifications */
  private List<String> actions = new ArrayList<String>();

  /** Unifications deeper than this are printed.
   *  Set it to -1 if you never want to print them.
   */
  public static int printDepth_ = -1;

  /** Unifications deeper than this fail!
   *  This is a convenient way of detecting infinite loops
   *  in the unification algorithms.
   *  Set it to -1 to turn off this feature.
   */
  public static int maxDepth_ = -1;

  /** Builds a message that describes one unification step.
   *  This is for debugging.
   */
  private boolean logAction(int depth, String msg, Object o1, Object o2, boolean result)
  {
    StringBuffer spaces = new StringBuffer();
    for (; depth > 0; depth--)
      spaces.append("  ");
    actions.add(spaces + msg + o1 + " = " + o2 + " -> "+result);
    return result;
  }

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
    actions.clear();
    boolean result = unify(o1, o2, 0);
    if (printDepth_ >= 0 && actions.size() > printDepth_)
    {
      Logger log = Logger.getLogger(getClass().getName());
      log.finer("UnifyObjects("+o1+", "+o2+") gives "+result);
      for (int i=actions.size()-1; i>=0; i--)
        log.finest(actions.get(i));
    }
    return result;
  }

  private boolean unify(Object o1, Object o2, int depth)
  {
    if (o1 == null && o2 == null) {
      logAction(depth, "both null", o1, o2, true);
      return true;
    }
    if (o1 != null && o2 != null) {
      if (o1 instanceof Term && o2 instanceof Term) {
        return unify((Term) o1, (Term) o2, depth);
      }
      if (! o1.equals(o2)) {
        notEqualObjectsFailure(o1, o2);
        logAction(depth, "notEqual: ", o1, o2, false);
        return false;
      }
      logAction(depth, "equal: ", o1, o2, true);
      return true;
    }
    notTermsFailure(o1, o2);
    logAction(depth, "notTerms: ", o1, o2, false);
    return false;
  }

  /**
   * Unifies two terms (with occurs check).
   *
   * @param term1 the first term.
   * @param term2 the second term.
   * @return <code>true</code> if both terms unify,
   *         <code>false</code> otherwise.
   */
  public boolean unify(Term term1, Term term2)
  {
    actions.clear();
    boolean result = unify(term1, term2, 0);
    if (printDepth_ >= 0 && actions.size() > maxDepth_)
    {
      Logger log = Logger.getLogger(getClass().getName());
      log.finer("UnifyTerms("+term1+", "+term2+") gives "+result);
      for (int i=actions.size()-1; i>=0; i--)
        log.finest(actions.get(i));
    }
    return result;
  }

  private boolean unify(Term term1, Term term2, int depth)
  {
    if (maxDepth_ >= 0 && depth > maxDepth_)
    {
      logAction(depth, "DEPTH "+maxDepth_+" EXCEEDED", term1, term2, false);
      return false;
    }
    Packer packer = new Packer();
    term1 = term1.accept(packer);
    term2 = term2.accept(packer);
    if (term1 == term2) {
      logAction(depth, "== ", term1, term2, true);
      return true;
    }
    if (term1 instanceof Joker) {
      return handleJoker((Joker) term1, term2, depth+1);
    }
    if (term2 instanceof Joker) {
      return handleJoker((Joker) term2, term1, depth+1);
    }
    ChildExtractor visitor = new ChildExtractor();
    Object[] args1 = term1.accept(visitor);
    Object[] args2 = term2.accept(visitor);
    if (args1.length == args2.length) {
      for (int i = 0; i < args1.length; i++) {
        boolean result = unify(args1[i], args2[i], depth+2);
        logAction(depth+2, "child "+i+": ", args1[i], args2[i], result);
        if (! result) {
          childrenFailure(term1, term2, i);
          return false;
        }
      }
    }
    else {
      numChildrenFailure(term1, term2);
      logAction(depth, ""+args1.length+"/="+args2.length, term1, term2, false);
      return false;
    }
    // logAction(depth, "ok ", term1, term2, true);
    return true;
  }

  /** Unifies a joker with a term.
   *  Does an occurs check to ensure that the joker
   *  does not already appear inside the term.
   * @param joker
   * @param term
   * @return true if they were unified.
   */
  private boolean handleJoker(Joker joker, Term term, int depth)
  {
    Term boundTo = joker.boundTo();
    if (boundTo != null) {
      boolean result = unify(boundTo, term, depth);
      logAction(depth, joker.toString()+" boundTo ", boundTo, term, result);
      return result;
    }
    if (term instanceof Wrapper) {
      term = ((Wrapper) term).getContent();
    }
    try {
      if (occursCheck.contains(term, joker))
      {
        logAction(depth, "occursCheckFailed: ", term, joker, false);
        return false;
      }
      else
      {
        Binding bind = joker.bind(term);
        bindings_.add(bind);
        logAction(depth, "Bind ", joker, term, true);
        return true;
      }
    }
    catch (IllegalArgumentException e) {
      jokerBindingFailure(joker, term, e);
      logAction(depth, "jokerBindingFailure: ", joker, term, false);
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
      cause_ = new UnificationException(left, right, message, cause);
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
