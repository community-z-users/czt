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
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * <p>A simple implementation of the Prover interface.</p>
 *
 * <p>This prover tries to prove a PredSequent by searching for an
 * applicable rule and, when one is found, tries to prove the new goals
 * created with the application of the rule.  It uses depth-first
 * search.</p>
 *
 * @author Petra Malik
 */
public class SimpleProver
  implements Prover
{
  private List<Rule> rules_;
  private Factory factory_;

  public SimpleProver(List<Rule> rules, Factory factory)
  {
    rules_ = rules;
    factory_ = factory;
  }

  /**
   * Tries all known rules to prove the sequent.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(PredSequent predSequent)
  {
    for (Iterator<Rule> i = rules_.iterator(); i.hasNext(); ) {
      Rule rule = i.next();
      Rule copiedRule = (Rule) copy(rule, new Factory(new ProverFactory()));
      try {
        boolean success = applyRule(copiedRule, predSequent, factory_);
        if (success && prove(predSequent.getDeduction())) {
          return true;
        }
      }
      catch (IllegalArgumentException e) {
        // PredSequent cannot be applied to this rule
      }
    }
    return false;
  }

  /**
   * Tries to prove a deduction by proving all its children.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(Deduction deduction)
  {
    if (prove(deduction.getSequent())) return true;
    return false;
  }

  /**
   * Tries to prove an array of sequents.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   *
   * Only handles PredSequent so far.
   */
  public boolean prove(List sequents)
  {
    for (Iterator i = sequents.iterator(); i.hasNext(); ) {
      Sequent sequent = (Sequent) i.next();
      if (sequent instanceof PredSequent) {
        if (! prove((PredSequent) sequent)) return false;
      }
      if (sequent instanceof ProverProviso) {
        ProverProviso proviso = (ProverProviso) sequent;
        proviso.check();
        if (! ProverProviso.Status.PASS.equals(proviso.getStatus())) {
          return false;
        }
      }
      else {
        System.err.println("Unsupported sequent " + sequent.getClass());
        return false;
      }
    }
    return true;
  }

  /**
   * Tries to apply a given Rule to a given PredSequent.
   * The factory is used to create the Deduction object.
   */
  public static boolean applyRule(Rule rule,
                                  PredSequent predSequent,
                                  Factory factory)
  {
    if (predSequent.getDeduction() != null) {
      String message = "A rule has been already applied to this PredSequent.";
      throw new IllegalStateException(message);
    }
    List sequents = rule.getSequent();
    try {
      Sequent sequent = (Sequent) sequents.remove(0);
      if (sequent instanceof PredSequent) {
        Pred pred = ((PredSequent) sequent).getPred();
        Set<Binding> bindings = new HashSet<Binding>();
        List<Binding> bindingList = new ArrayList<Binding>();
        bindingList.addAll(bindings);
        if (unify(pred, predSequent.getPred(), bindings)) {
          Deduction deduction =
            factory.createDeduction(bindingList, sequents, rule.getName());
          predSequent.setDeduction(deduction);
          return true;
        }
      }
      else {
        String message = "Conclusion of a rule must be a PredSequent";
        throw new IllegalArgumentException(message);
      }
    }
    catch (IndexOutOfBoundsException exception) {
      throw new IllegalArgumentException("Rule without Sequent");
    }
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
      return false;
    }
    Object[] args1 = term1.getChildren();
    Object[] args2 = term2.getChildren();
    for (int i = 0; i < args1.length; i++) {
      if (args1[i] == null && args2[i] != null) {
        return false;
      }
      if (args2[i] == null && args1[i] != null) {
        return false;
      }
      if (args1[i] != null) {
        if (args1[i] instanceof Term) {
          Term child1 = (Term) args1[i];
          Term child2 = (Term) args2[i];
          if (! unify(child1, child2, bindings)) {
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

  private static boolean handleJoker(Joker joker, Term term,
                                     Set<Binding> bindings)
  {
    Term boundTo = joker.boundTo();
    if (boundTo != null) {
      return unify(boundTo, term, bindings);
    }
    try {
      bindings.add(joker.bind(term));
      return true;
    }
    catch (IllegalArgumentException e) {
      return false;
    }
  }

  public static Term copy(Term term, Factory factory)
  {
    CopyVisitor visitor = new CopyVisitor(factory);
    return (Term) term.accept(visitor);
  }

  /**
   * A visitor that copies a term and uses the given factory to create
   * new Joker.  Currently, JokerExpr, JokerName, and JokerPred are supported.
   */
  public static class CopyVisitor
    implements TermVisitor,
	       JokerPredVisitor,
	       JokerExprVisitor
  {
    private Factory factory_;

    public CopyVisitor(Factory factory)
    {
      factory_ = factory;
    }

    public Object visitTerm(Term term)
    {
      return VisitorUtils.visitTerm(this, term, false);
    }

    public Object visitJokerExpr(JokerExpr joker)
    {
      return factory_.createJokerExpr(joker.getName());
    }

    public Object visitJokerName(JokerName joker)
    {
      return factory_.createJokerName(joker.getWord(),
                                      joker.getStroke(),
                                      joker.getId(),
                                      joker.getName());
    }

    public Object visitJokerPred(JokerPred joker)
    {
      return factory_.createJokerPred(joker.getName());
    }

    public Object visitLookupConstDeclProviso(LookupConstDeclProviso proviso)
    {
      return factory_.createLookupConstDeclProviso(proviso.getSequentContext(),
                         (Expr) proviso.getLeftExpr().accept(this),
                         (Expr) proviso.getRightExpr().accept(this));
    }
  }
}
