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

package net.sourceforge.czt.rules.rewriter;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.oracles.AbstractOracle;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.prover.SimpleProver;
import net.sourceforge.czt.rules.unification.UnificationUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ConcreteSyntaxSymbol;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.SyntaxSymbolVisitor;
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
             ExprVisitor<Term>,
             PredVisitor<Term>
{
  private Map<ConcreteSyntaxSymbol,List<RewriteRule>> exprRules_ =
    new HashMap<ConcreteSyntaxSymbol,List<RewriteRule>>();
  private Map<ConcreteSyntaxSymbol,List<RewriteRule>> predRules_ =
    new HashMap<ConcreteSyntaxSymbol,List<RewriteRule>>();
  private List<Oracle> oracles_ = new ArrayList<Oracle>();
  private SectionManager manager_;
  private String section_;
  @SuppressWarnings("unused")
private SimpleProver prover_;
  private SyntaxSymbolVisitor visitor_ = new SyntaxSymbolVisitor();

  /**
   * @throws CommandException if the given sectionmanager doesn't provide
   *                          SectTypeEnv information for the given section.
   */
  public RewriteVisitor(RuleTable rules,
                        SectionManager manager,
                        String section)
    throws CommandException
  {
    for (Iterator<RulePara> iter = rules.iterator(); iter.hasNext(); ) {
      RulePara rulePara = iter.next();
      // Assuming oracles are not directly used for rewriting
      if (rulePara instanceof Rule) {
        Factory factory = new Factory(new ProverFactory());
        CopyVisitor copyVisitor = new CopyVisitor(factory);
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
    manager_ = manager;
    section_ = section;
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

  public Term visitExpr(Expr expr)
  {
    return rewrite(expr, exprRules_);
  }

  public Term visitPred(Pred pred)
  {
    return rewrite(pred, predRules_);
  }

  public Term rewrite(Term term,
                      Map<ConcreteSyntaxSymbol,List<RewriteRule>> map)
  {
    ConcreteSyntaxSymbol key = term.accept(visitor_);
    if (key == null) {
      throw new IllegalStateException("Cannot handle term " + term);
    }
    return rewrite(term, map.get(key));
  }

  @SuppressWarnings("unused")
private void checkTypes(Term term1, Term term2)
  {
    PrintVisitor printer = new PrintVisitor();
    printer.setPrintIds(true);
    if (term1 == null || term2 == null) return;
    TypeAnn type1 = term1.getAnn(TypeAnn.class);
    if (type1 != null) {
      TypeAnn type2 = term2.getAnn(TypeAnn.class);
      if (type2 == null ||
          (UnificationUtils.unify(type1, type2) != null &&
          (type1.getType() instanceof PowerType) &&
          ((PowerType) type1.getType()).getType() instanceof SchemaType)) {
        for (Iterator<?> iter = term2.getAnns().iterator(); iter.hasNext(); ) {
          if (iter.next() instanceof TypeAnn) {
            iter.remove();
          }
        }
        Factory factory = new Factory(new ProverFactory());
        CopyVisitor copyVisitor = new CopyVisitor(factory);
        type2 = (TypeAnn) type1.accept(copyVisitor);
        term2.getAnns().add(type2);
      }
      if (! type1.equals(type2)) {
        System.err.println("Type1 " + type1.accept(printer));
        System.err.println("Type2 " +
                           ((type2 != null) ? type2.accept(printer) : "null"));
      }
    }
  }

  public Term rewrite(Term term, List<RewriteRule> rules)
  {
    if (rules != null) {
      for (RewriteRule rule : rules) {
        Term result = rule.apply(term);
        if (result != null) {
          // TODO: add this back in and investigate why some types are not equal
          //checkTypes(term, result);
          return result;
        }
      }
    }
    return null;
  }

  public class RewriteRule
  {
    private String name_;
    private Term left_;
    private Term right_;
    private List<OracleAppl> appls_ = new ArrayList<OracleAppl>();

    public RewriteRule(String name,
                       Term left,
                       Term right,
                       SequentList provisos)
    {
      name_ = name;
      left_ = left;
      right_ = right;
      for (Sequent sequent : provisos) {
        boolean foundOracle = false;
        for (Oracle oracle : oracles_) {
          if (SimpleProver.apply(oracle, sequent)) {
            OracleAppl oracleAppl = sequent.getAnn(OracleAppl.class);
            foundOracle = true;
            appls_.add(oracleAppl);
            break;
          }
        }
        if (! foundOracle) {
          String message = "Rule " + name + ": No oracle found";
          throw new IllegalStateException(message);
        }
      }
    }

    public String getName()
    {
      return name_;
    }

    private void undo(Set<Binding> bindings)
    {
      ProverUtils.reset(bindings);
    }

    public Term apply(Term term)
    {
      Set<Binding> bindings = UnificationUtils.unify(left_, term);
      if (bindings == null) {
        return null;
      }
      for (OracleAppl oracleAppl : appls_) {
        AbstractOracle checker =
          ProverUtils.ORACLES.get(oracleAppl.getName());
        if (checker != null) {
          @SuppressWarnings("unchecked")
		List<? extends Term> args = (List<? extends Term>)oracleAppl.getAnn(List.class);
          try {
            Set<Binding> bdgs = checker.check(args, manager_, section_);
            if (bdgs != null) {
              bindings.addAll(bdgs);
            }
            else {
              undo(bindings);
              return null;
            }
          }
          catch (UnboundJokerException e) {
            // String msg = "Rule " + name_ +
            //   ": UnboundJokerException from oracle " +
            //   oracleAppl.getName();
            // System.err.println(msg);
            // System.err.println(e.getMessage());
            undo(bindings);
            return null;
          }
        }
      }
      try {
        Term result = ProverUtils.removeJoker(right_);
        undo(bindings);
        //        StringWriter out = new StringWriter();
        //        out.write("Rewrite ");
        //        PrintUtils.printLatex(term, out, manager_, section_);
        //        out.write(" to ");
        //        PrintUtils.printLatex(result, out, manager_, section_);
        //        out.write(" using rule " + name_);
        //        System.err.println(out.toString());
        return result;
      }
      catch (UnboundJokerException e) {
        System.err.println("Result of rewrite rule contains jokers");
        undo(bindings);
        throw new RuntimeException(e);
      }
    }
  }

  public class AddRuleVisitor
    implements ExprVisitor<Object>,
               PredVisitor<Object>
  {
    private RewriteRule rule_;

    public AddRuleVisitor(RewriteRule rule)
    {
      rule_ = rule;
    }

    private void addRule(Term term,
                         Map<ConcreteSyntaxSymbol,List<RewriteRule>> map)
    {
      ConcreteSyntaxSymbol key = term.accept(visitor_);
      if (key == null) {
        String msg = "Rule " + rule_.getName() +
          ": Cannot handle term " + term;
        throw new IllegalStateException(msg);
      }
      addRule(key, map);
    }

    private void addRule(ConcreteSyntaxSymbol key,
                         Map<ConcreteSyntaxSymbol,List<RewriteRule>> map)
    {
      List<RewriteRule> rules = map.get(key);
      if (rules != null) {
        rules.add(rule_);
      }
      else {
        rules = new ArrayList<RewriteRule>();
        rules.add(rule_);
        map.put(key, rules);
      }
    }

    public Object visitExpr(Expr expr)
    {
      addRule(expr, exprRules_);
      return null;
    }

    public Object visitPred(Pred pred)
    {
      addRule(pred, predRules_);
      return null;
    }
  }
}
