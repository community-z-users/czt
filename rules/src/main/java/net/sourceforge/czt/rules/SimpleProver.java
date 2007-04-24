/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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
import net.sourceforge.czt.util.CztException;
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
  private Random rand_ = new Random();  // used just for log messages

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

  public String getSection()
  {
    return section_;
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
    PredSequent predSequent =
      ProverUtils.createPredSequent(pred, true);
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
    for (Iterator<RulePara> iter = rules_.iterator(); iter.hasNext(); ) {
      RulePara rulePara = iter.next();
      try {
        boolean success = apply(rulePara, predSequent);
        if (success) {
          // we use a random id number in log messages to make it
          // clearer which rule application each message is talking about.
          int id = rand_.nextInt(1000);
          Deduction ded = predSequent.getDeduction();
          if (ded instanceof RuleApplication) {
            RuleApplication ruleAppl = (RuleApplication) ded;
            String message = "Applied rule " + rulePara.getName() + "." + id
              + ", children=" + ruleAppl.getSequentList().size();
            getLogger().fine(message);
            int problem = prove(ruleAppl.getSequentList());
            if (problem < 0) {
              message = "Finished rule " + rulePara.getName() + "." + id;
              getLogger().fine(message);
              return true;
            }
            else {
              undo(predSequent);
              message = "Undid rule " + rulePara.getName() + "." + id
                + " because antecedent " + problem + " failed";
              getLogger().fine(message);
            }
          }
          else if (ded instanceof ProvisoApplication) {
            if (prove((ProvisoApplication) ded)) return true;
            undo(predSequent);
          }
          else {
            throw new CztException("Unsupported deduction " + ded);
          }
        }
      }
      catch (IllegalArgumentException e) {
        String message =
          "PredSequent cannot be applied to rule " + rulePara.getName() + ": "
          + e.getMessage();
        getLogger().warning(message);
      }
    }
    return false;
  }

  /**
   * Undos the bindings of the duduction and sets deduction to null.
   * Note that this method does not iterate into the children of a
   * deduction, so only undoes the bindings of this deduction.
   */
  public void undo(PredSequent predSequent)
  {
    Deduction deduction = predSequent.getDeduction();
    if (deduction == null) return;
    if (deduction instanceof RuleApplication) {
      RuleApplication ruleAppl = (RuleApplication) deduction;
      ProverUtils.reset(ruleAppl.getBinding());
      predSequent.setDeduction(null);
    }
    else if (deduction instanceof ProvisoApplication) {
      ProvisoApplication provisoAppl = (ProvisoApplication) deduction;
      ProverUtils.reset(provisoAppl.getBinding());
      predSequent.setDeduction(null);
    }
    else {
      throw new CztException("Unsupported deduction " + deduction);
    }
  }

  /**
   * Tries to prove a deduction by proving all its children.
   * Returns <code>true</code> if this succeeds,
   * otherwise it returns false.
   */
  public boolean prove(Deduction deduction)
  {
    if (deduction instanceof RuleApplication) {
      RuleApplication ruleAppl = (RuleApplication) deduction;
      return prove(ruleAppl.getSequentList()) < 0;
    }
    else if (deduction instanceof ProvisoApplication) {
      return prove((ProvisoApplication) deduction);
    }
    throw new CztException("Unsupported deduction " + deduction);
  }

  public boolean prove(ProvisoApplication proviso)
  {
    ProvisoStatus status = proviso.getProvisoStatus();
    if (status instanceof CheckPassed) return true;
    // TODO: All provisos fail right now!
    return false;
  }

  /**
   * Tries to prove an array of sequents.
   * Returns <code>-1</code> if this succeeds,
   * otherwise it returns the number of the sequent
   * that failed (from 0 upwards).
   */
  public int prove(SequentList sequents)
  {
    int result = -1;
    for (Sequent sequent : sequents) {
      result++;
      if (sequent instanceof PredSequent) {
        if (! prove((PredSequent) sequent)) return result;
      }
      else if (sequent instanceof ProverProviso) {
        ProverProviso proviso = (ProverProviso) sequent;
        proviso.check(manager_, section_);
        if (! ProverProviso.Status.PASS.equals(proviso.getStatus())) {
          return result;
        }
      }
      else {
        return result;
      }
    }
    return -1;
  }

  public static boolean apply(RulePara rulePara, PredSequent predSequent)
  {
    if (rulePara instanceof Rule) {
      return apply((Rule) rulePara, predSequent);
    }
    else if (rulePara instanceof Proviso2) {
      return apply((Proviso2) rulePara, predSequent);
    }
    return false;
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
      String message =
        "This PredSequent already has a deduction associated to it.";
      throw new IllegalArgumentException(message);
    }
    // Note: must use new ProverFactory here to generate fresh joker names.
    Factory factory = new Factory(new ProverFactory());
    rule = (Rule) copy(rule, factory);
    Sequent sequent = rule.getSequent();
    if (sequent instanceof PredSequent) {
      Pred pred = ((PredSequent) sequent).getPred();
      Set<Binding> bindings =
        UnificationUtils.unify(pred, predSequent.getPred());
      if (bindings != null) {
        List<Binding> bindingList = new ArrayList<Binding>();
        bindingList.addAll(bindings);
        RuleApplication ruleAppl =
          factory.createRuleApplication(bindingList,
                                        rule.getAntecedents(),
                                        rule.getName());
        predSequent.setDeduction(ruleAppl);
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
   * Tries to apply a given Proviso to a given PredSequent.
   * The factory is used to create the Deduction object.
   *
   * @throws IllegalArgumentException if a rule has already been applied to
   *                                  predSequent or the conclusion of the
                                      rule is not a PredSequent.
   */
  public static boolean apply(Proviso2 proviso, PredSequent predSequent)
  {
    if (predSequent.getDeduction() != null) {
      String message =
        "This PredSequent already has a deduction associated to it.";
      throw new IllegalArgumentException(message);
    }
    // Note: must use new ProverFactory here to generate fresh joker names.
    Factory factory = new Factory(new ProverFactory());
    proviso = (Proviso2) copy(proviso, factory);
    Sequent sequent = proviso.getSequent();
    if (sequent instanceof PredSequent) {
      Pred pred = ((PredSequent) sequent).getPred();
      Set<Binding> bindings =
        UnificationUtils.unify(pred, predSequent.getPred());
      if (bindings != null) {
        List<Binding> bindingList = new ArrayList<Binding>();
        bindingList.addAll(bindings);
        ProvisoApplication provisoAppl =
          factory.createProvisoApplication(bindingList,
                                           null,
                                           proviso.getName());
        predSequent.setDeduction(provisoAppl);
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
        String message =
          "This PredSequent already has a deduction associated to it.";
        throw new IllegalArgumentException(message);
      }
      // Note: must use new ProverFactory here to generate fresh joker names.
      Factory factory = new Factory(new ProverFactory());
      rule = (Rule) copy(rule, factory);
      Sequent sequent = rule.getSequent();
      if (sequent instanceof PredSequent) {
        Pred pred = ((PredSequent) sequent).getPred();
        Set<Binding> bindings =
          UnificationUtils.unify2(pred, predSequent.getPred());
        if (bindings != null) {
          List<Binding> bindingList = new ArrayList<Binding>();
          bindingList.addAll(bindings);
          Deduction deduction =
            factory.createRuleApplication(bindingList,
                                          rule.getAntecedents(),
                                          rule.getName());
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
