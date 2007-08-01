/*
  Copyright (C) 2007 Petra Malik
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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.unification.UnificationUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * Returns a rewritten version of the given term.  Note
 * that this is not recursive, i.e. the children of the term
 * are not rewritten.  If the rewriting fails, the apply method
 * returns the given term itself while the visit methods return
 * <code>null</code>.  Note also that the term returned by the
 * visit methods may contain jokers.
 */
public class RewriteVisitor
  implements Rewriter,
             TermVisitor<Term>,
             AndExprVisitor<Term>,
             AndPredVisitor<Term>,
             ExprVisitor<Term>,
             NegPredVisitor<Term>,
             OrPredVisitor<Term>,
             PredVisitor<Term>,
             QntExprVisitor<Term>,
             QntPredVisitor<Term>,
             RenameExprVisitor<Term>
{
  private List<RewriteRule> andExprRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> andPredRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> exprRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> negPredRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> orPredRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> predRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> qntExprRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> qntPredRules_ = new ArrayList<RewriteRule>();
  private List<RewriteRule> renameExprRules_ = new ArrayList<RewriteRule>();

  private List<Oracle> oracles_ = new ArrayList<Oracle>();
  private SimpleProver prover_;

  public RewriteVisitor(RuleTable rules,
                        SectionManager manager,
                        String section)
  {
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor copyVisitor = new CopyVisitor(factory);
    for (Iterator<RulePara> iter = rules.iterator(); iter.hasNext(); ) {
      RulePara rulePara = iter.next();
      // Assuming oracles are not directly used for rewriting
      if (rulePara instanceof Rule) {
        Rule rule = (Rule) rulePara.accept(copyVisitor);
        Sequent conclusion = rule.getSequent();
        Pred pred = conclusion.getPred();
        if (pred instanceof IffPred) {
          IffPred iff = (IffPred) pred;
          Pred left = iff.getLeftPred();
          Pred right = iff.getRightPred();
          RewriteRule rewriteRule =
            new RewriteRule(rule.getName(), left, right, rule.getPremisses());
          left.accept(new AddRuleVisitor(rewriteRule));
        }
        else if (pred instanceof MemPred) {
          MemPred memPred = (MemPred) pred;
          Expr left = memPred.getLeftExpr();
          if (memPred.getRightExpr() instanceof SetExpr) {
            SetExpr set = (SetExpr) memPred.getRightExpr();
            if (set.getZExprList().size() == 1) {
              Expr right = set.getZExprList().get(0);
              RewriteRule rewriteRule =
                new RewriteRule(rule.getName(), left, right,
                                rule.getPremisses());
              left.accept(new AddRuleVisitor(rewriteRule));
            }
            else {
              System.err.println("Ignoring " + rule.getName());
              System.err.println("Set contains more than one element");
            }
          }
          else {
            System.err.println("Ignoring " + rule.getName());
            System.err.println("Right expr is " + memPred.getRightExpr());
          }
        }
        else {
          System.err.println("Ignoring " + rule.getName());
        }
      }
      else if (rulePara instanceof Oracle) {
        oracles_.add((Oracle) rulePara);
      }
    }
    prover_ = new SimpleProver(null, manager, section);
  }

  public Term rewrite(Term term)
    throws UnboundJokerException
  {
    try {
      Term result = term.accept(this);
      if (result == null) return term;
      return result;
    }
    catch (RuntimeException e) {
      if (e.getCause() instanceof UnboundJokerException) {
        throw (UnboundJokerException) e.getCause();
      }
      throw e;
    }
  }

  public Term visitTerm(Term term)
  {
    return term;
  }

  public Term visitAndExpr(AndExpr term)
  {
    return rewrite(term, andExprRules_);
  }

  public Term visitAndPred(AndPred term)
  {
    return rewrite(term, andPredRules_);
  }

  public Term visitExpr(Expr expr)
  {
    return rewrite(expr, exprRules_);
  }

  public Term visitNegPred(NegPred pred)
  {
    return rewrite(pred, negPredRules_);
  }

  public Term visitOrPred(OrPred pred)
  {
    return rewrite(pred, orPredRules_);
  }

  public Term visitPred(Pred pred)
  {
    return rewrite(pred, predRules_);
  }

  public Term visitQntExpr(QntExpr term)
  {
    return rewrite(term, qntExprRules_);
  }

  public Term visitQntPred(QntPred pred)
  {
    return rewrite(pred, qntPredRules_);
  }

  public Term visitRenameExpr(RenameExpr term)
  {
    return rewrite(term, renameExprRules_);
  }

  public Term rewrite(Term term, List<RewriteRule> rules)
  {
    for (RewriteRule rule : rules) {
      Term result = rule.apply(term);
      if (result != null) return result;
    }
    return null;
  }

  public class RewriteRule
  {
    private String name_;
    private Term left_;
    private Term right_;
    private SequentList provisos_;

    public RewriteRule(String name,
                       Term left,
                       Term right,
                       SequentList provisos)
    {
      name_ = name;
      left_ = left;
      right_ = right;
      provisos_ = provisos;
    }

    private void undo(Set<Binding> bindings)
    {
      ProverUtils.reset(bindings);
      for (Sequent sequent : provisos_)
      {
        prover_.undo(sequent);
      }
    }

    public Term apply(Term term)
    {
      Set<Binding> bindings = UnificationUtils.unify(left_, term);
      if (bindings == null) return null;
      for (Sequent sequent : provisos_) {
        boolean proved = false;
        for (Oracle oracle : oracles_) {
          if (SimpleProver.apply(oracle, sequent)) {
            OracleAppl oracleAppl = sequent.getAnn(OracleAppl.class);
            if (prover_.prove(oracleAppl)) {
              proved = true;
              break;
            }
            else {
              prover_.undo(sequent);
            }
          }
        }
        if (! proved) {
          undo(bindings);
          return null;
        }
      }
      try {
        Term result = ProverUtils.removeJoker(right_);
        undo(bindings);
        return result;
      }
      catch (UnboundJokerException e) {
        undo(bindings);
        throw new RuntimeException(e);
      }
    }
  }

  public class AddRuleVisitor
    implements AndExprVisitor<Object>,
               AndPredVisitor<Object>,
               ExprVisitor<Object>,
               NegPredVisitor<Object>,
               OrPredVisitor<Object>,
               PredVisitor<Object>,
               QntExprVisitor<Object>,
               QntPredVisitor<Object>,
               RenameExprVisitor<Object>
  {
    private RewriteRule rule_;

    public AddRuleVisitor(RewriteRule rule)
    {
      rule_ = rule;
    }

    public Object visitAndExpr(AndExpr andExpr)
    {
      andExprRules_.add(rule_);
      return null;
    }

    public Object visitAndPred(AndPred andPred)
    {
      andPredRules_.add(rule_);
      return null;
    }

    public Object visitExpr(Expr expr)
    {
      exprRules_.add(rule_);
      return null;
    }

    public Object visitNegPred(NegPred negPred)
    {
      negPredRules_.add(rule_);
      return null;
    }

    public Object visitOrPred(OrPred orPred)
    {
      orPredRules_.add(rule_);
      return null;
    }

    public Object visitPred(Pred pred)
    {
      predRules_.add(rule_);
      return null;
    }

    public Object visitQntExpr(QntExpr term)
    {
      qntExprRules_.add(rule_);
      return null;
    }

    public Object visitQntPred(QntPred term)
    {
      qntPredRules_.add(rule_);
      return null;
    }

    public Object visitRenameExpr(RenameExpr term)
    {
      renameExprRules_.add(rule_);
      return null;
    }
  }
}
