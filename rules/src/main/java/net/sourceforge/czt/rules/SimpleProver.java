/*
  Copyright (C) 2005, 2006 Petra Malik
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
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Session;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

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
  private RuleTable rules_;
  private SectionManager manager_;
  private String section_;

  public SimpleProver(Session session)
    throws CommandException
  {
    rules_ = (RuleTable) session.get(RuleTable.class);
    manager_ = session.getManager();
    section_ = session.getSection();
  }

  public SimpleProver(RuleTable rules,
                      SectionManager manager,
                      String section)
  {
    rules_ = rules;
    manager_ = manager;
    section_ = section;
  }

  private Logger getLogger()
  {
    return Logger.getLogger(getClass().getName());
  }

  /**
   * Tries to prove the given pred.  The predicate is first copied.
   */
  public boolean prove(Pred pred)
  {
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor copyVisitor = new CopyVisitor(factory);
    PredSequent predSequent =
      ProverUtils.createPredSequent((Pred) pred.accept(copyVisitor));
    return prove(predSequent);
  }

  /**
   * Tries all known rules to prove the sequent.
   * For each rule that matches the sequent, it
   * recursively proves all children.  If any
   * children cannot be proved, that rule is undone
   * and other rules are tried.  So this is the same
   * depth-first, left-first search (if one regards the
   * rules as being ordered left-to-right) that Prolog uses.
   * 
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(PredSequent predSequent)
  {
    for (Iterator<Rule> iter = rules_.iterator(); iter.hasNext(); ) {
      Rule rule = iter.next();
      String message = "Trying rule " + rule.getName();
      getLogger().finer(message);
      try {
        boolean success = apply(rule, predSequent);
        if (success && prove(predSequent.getDeduction())) {
          message = "Rule " + rule.getName() + " succeeded";
          getLogger().finer(message);
          return true;
        }
        else {
          undo(predSequent);
          message = "Rule " + rule.getName() + " failed";
          getLogger().finer(message);
       }
      }
      catch (IllegalArgumentException e) {
        message =
          "PredSequent cannot be applied to rule " + rule.getName() + ": "
          + e.getMessage();
        getLogger().warning(message);
      }
    }
    return false;
  }

  private void undo(PredSequent predSequent)
  {
    Deduction ded = predSequent.getDeduction();
    if (ded != null) {
      ProverUtils.reset(ded.getBinding());
      predSequent.setDeduction(null);
    }
  }

  /**
   * Tries to prove a deduction by proving all its children.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(Deduction deduction)
  {
    return prove(deduction.getSequent());
  }

  /**
   * Tries to prove an array of sequents.
   * Returns <code>true</code> if this succeeds,
   * <code>false</code> otherwise.
   */
  public boolean prove(List<Sequent> sequents)
  {
    for (Iterator<Sequent> i = sequents.iterator(); i.hasNext(); ) {
      Sequent sequent = i.next();
      if (sequent instanceof PredSequent) {
        if (! prove((PredSequent) sequent)) return false;
      }
      else if (sequent instanceof ProverProviso) {
        ProverProviso proviso = (ProverProviso) sequent;
        proviso.check(manager_, section_);
        if (! ProverProviso.Status.PASS.equals(proviso.getStatus())) {
          return false;
        }
      }
      else {
        return false;
      }
    }
    return true;
  }

  /**
   * Tries to apply a given Rule to a given PredSequent.
   * The factory is used to create the Deduction object.
   *
   * @throws IllegalArgumentException if a rule has already been applied to
   *                                  predSequent or the conclusion of the
                                      rule is not a PredSequent.
   */
  public static boolean apply(Rule rule, PredSequent predSequent)
  {
    if (predSequent.getDeduction() != null) {
      String message = "A rule has been already applied to this PredSequent.";
      throw new IllegalArgumentException(message);
    }
    // Note: must use new ProverFactory here to generate fresh joker names.
    Factory factory = new Factory(new ProverFactory());
    rule = (Rule) copy(rule, factory);
    List<Sequent> sequents = rule.getSequent();
    if (sequents.size() <= 0) {
      throw new IllegalArgumentException("Rule without Sequent");
    }
    Sequent sequent = sequents.remove(0);
    if (sequent instanceof PredSequent) {
      Pred pred = ((PredSequent) sequent).getPred();
      Set<Binding> bindings =
        UnificationUtils.unify(pred, predSequent.getPred());
      if (bindings != null) {
        List<Binding> bindingList = new ArrayList<Binding>();
        bindingList.addAll(bindings);
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
    return false;
  }

  /**
   *
   * @throws RuleApplicationException if the sequent of the rule and the rule
   *                                  do not unify
   * @throws IllegalArgumentException if a rule has already been applied to
   *                                  to the sequent,
   *                                  or the rule doesn't have a sequent
   */
  public static boolean apply2(Rule rule, PredSequent predSequent)
    throws RuleApplicationException
  {
    try {
      if (predSequent.getDeduction() != null) {
        String message = "A rule has been already applied to this PredSequent.";
        throw new IllegalArgumentException(message);
      }
      // Note: must use new ProverFactory here to generate fresh joker names.
      Factory factory = new Factory(new ProverFactory());
      rule = (Rule) copy(rule, factory);
      List<Sequent> sequents = rule.getSequent();
      if (sequents.size() <= 0) {
        throw new IllegalArgumentException("Rule without Sequent");
      }
      Sequent sequent = sequents.remove(0);
      if (sequent instanceof PredSequent) {
        Pred pred = ((PredSequent) sequent).getPred();
        Set<Binding> bindings =
          UnificationUtils.unify2(pred, predSequent.getPred());
        if (bindings != null) {
          List<Binding> bindingList = new ArrayList<Binding>();
          bindingList.addAll(bindings);
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
      return false;
    }
    catch (UnificationException e) {
      throw new RuleApplicationException(rule, predSequent, e);
    }
  }

  /**
   *
   * @throws NullPointerException if <code>term</code> is <code>null</code>.
   */
  public static Term copy(Term term, Factory factory)
  {
    CopyVisitor visitor = new CopyVisitor(factory);
    return term.accept(visitor);
  }
}
