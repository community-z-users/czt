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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * A simple deduction implementation that just handles JokerExpr and
 * JokerPred for now.
 *
 * @author Petra Malik
 */
public class DeductionImpl
  implements Deduction
{
  private String name_;
  private PredSequent conclusion_;
  private boolean valid_;
  private Sequent[] children_ = null;
  private List<JokerExpr> boundJokerExpr_ = new ArrayList();
  private List<JokerPred> boundJokerPred_ = new ArrayList();

  /**
   * @throws IllegalArgumentException if rule does not have a Sequent.
   */
  public DeductionImpl(Rule rule, PredSequent conclusion)
  {
    name_ = rule.getName();
    CopyVisitor visitor = new CopyVisitor();
    Rule copiedRule = (Rule) rule.accept(visitor);
    ListTerm list = (ListTerm) copiedRule.getSequent().accept(visitor);
    try {
      Sequent sequent = (Sequent) list.remove(0);
      if (match(sequent, conclusion)) {
	valid_ = true;
	children_ = (Sequent[]) list.toArray(new Sequent[0]);
      }
      else {
	undoBindings();
	valid_ = false;
      }
    }
    catch (IndexOutOfBoundsException exception) {
      throw new IllegalArgumentException("Rule without Sequent");
    }
    conclusion_ = conclusion;
  }

  private void undoBindings()
  {
    for (Iterator<JokerExpr> i = boundJokerExpr_.iterator(); i.hasNext();) {
      JokerExpr joker = i.next();
      joker.setBinding(null);
    }
    for (Iterator<JokerPred> i = boundJokerPred_.iterator(); i.hasNext();) {
      JokerPred joker = i.next();
      joker.setBinding(null);
    }
  }

  public String getName()
  {
    return name_;
  }

  public void next()
  {
    undoBindings();
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
   * Matches two terms (no occur check).
   *
   * @param term1 the first term.
   * @param term2 the second term.
   * @return <code>true</code> if both term match, 
   *         <code>false</code> otherwise.
   */
  private boolean match(Term term1, Term term2)
  {
    if (term1 == term2) {
      return true;
    }
    if (term1 instanceof JokerExpr) {
      return handleJokerExpr((JokerExpr) term1, term2);
    }
    if (term2 instanceof JokerExpr) {
      return handleJokerExpr((JokerExpr) term2, term1);
    }
    if (term1 instanceof JokerPred) {
      return handleJokerPred((JokerPred) term1, term2);
    }
    if (term2 instanceof JokerPred) {
      return handleJokerPred((JokerPred) term2, term1);
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
        else {
          if (! args1[i].equals(args2[i])) {
            return false;
          }
        }
      }
    }
    return true;
  }

  private boolean handleJokerExpr(JokerExpr joker, Term term)
  {
    if (joker.getBinding() != null) {
      return match(joker.getBinding(), term);
    }
    if (term instanceof Expr) {
      joker.setBinding((Expr) term);
      boundJokerExpr_.add(joker);
      return true;
    }
    return false;
  }

  private boolean handleJokerPred(JokerPred joker, Term term)
  {
    if (joker.getBinding() != null) {
      return match(joker.getBinding(), term);
    }
    if (term instanceof Pred) {
      joker.setBinding((Pred) term);
      boundJokerPred_.add(joker);
      return true;
    }
    return false;
  }

  /**
   * A visitor that copies a term.
   */
  private class CopyVisitor
    implements TermVisitor,
	       JokerPredVisitor,
	       JokerExprVisitor
  {
    private Factory factory_ = new Factory();
    private Map<String, JokerExpr> exprJoker_ = new HashMap();
    private Map<String, JokerPred> predJoker_ = new HashMap();

    public Object visitTerm(Term term)
    {
      return VisitorUtils.visitTerm(this, term, false);
    }

    public Object visitJokerExpr(JokerExpr joker)
    {
      JokerExpr result = exprJoker_.get(joker.getName());
      if (result == null) {
	exprJoker_.put(joker.getName(), joker);
	result = joker;
      }
      return result;
    }

    public Object visitJokerPred(JokerPred joker)
    {
      JokerPred result = predJoker_.get(joker.getName());
      if (result == null) {
	predJoker_.put(joker.getName(), joker);
	result = joker;
      }
      return result;
    }
  }
}
