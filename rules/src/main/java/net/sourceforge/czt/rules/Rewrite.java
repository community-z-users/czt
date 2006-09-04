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

package net.sourceforge.czt.rules;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;

/**
 * <p>A rewrite engine for Z terms.</p>
 *
 * <p>Given a set or rules and a term (AST), this engine rewrites the
 * term using the rules.  It rewrites each level of the term in a
 * top-down fashion.
 *
 * It tries the rules in the order that they appear in the
 * specification and commits to the first matching rule.
 * If there are no matching rules, the expression is left unchanged.
 * An expression can be rewritten by several rules in succession.
 *
 * @author Petra Malik
 */
public class Rewrite
  implements TermVisitor<Term>,
             ExprVisitor<Term>,
             SchTextVisitor<Term>,
             PredVisitor<Term>,
             ZSectVisitor<Term>
{
  /** Maximum number of rewrites of the same expr/pred.
   *  If more rules than this are used, we assume that
   *  there is an infinite loop in the rules.
   */
  private int MAX_REWRITES = 20;

  private SectionManager manager_;

  private RuleTable rules_;

  private String section_;

  /** The name of the schema text equality operator: schemaEquals. */
  private static RefExpr schemaEqualsRefExpr_;

  public Rewrite(SectionManager manager, RuleTable rules)
  {
    VisitorUtils.checkVisitorRules(this);
    manager_ = manager;
    rules_ = rules;
    Factory factory = new Factory(new ProverFactory());
    String schemaEqOp = ZString.ARG_TOK + "schemaEquals" + ZString.ARG_TOK;
    StrokeList noStrokes = factory.createZStrokeList();
    ZDeclName declName = factory.createZDeclName(schemaEqOp, noStrokes, "global");
    ZRefName refName = factory.createZRefName(schemaEqOp, noStrokes, declName);
    schemaEqualsRefExpr_ = factory.createRefExpr(refName);
  }

  public Term visitZSect(ZSect zSect)
  {
    section_ = zSect.getName();
    return VisitorUtils.visitTerm(this, zSect, true);
  }

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Term visitExpr(Expr expr)
  {
    Expr oldExpr = expr;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldExpr = expr;
      expr = (Expr) rewriteOnce(manager_, section_, expr, rules_);
      rewrites++;
      if (rewrites > MAX_REWRITES)
        throw new RuntimeException("Infinite loop in rules on expr "+expr);
    } while (expr != oldExpr);
    // now recurse into subexpressions
    return VisitorUtils.visitTerm(this, expr, true);
  }

  public Term visitPred(Pred pred)
  {
    Pred oldPred = pred;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldPred = pred;
      pred = (Pred) rewriteOnce(manager_, section_, pred, rules_);
      rewrites++;
      if (rewrites > MAX_REWRITES)
        throw new RuntimeException("Infinite loop in rules on pred "+pred);
    } while (pred != oldPred);
    // now recurse into subexpressions
    return VisitorUtils.visitTerm(this, pred, true);
  }

  /** This rewrites schema text, using rules with conclusions
   *  of the form [D1|P1] \schemaEquals [D2|P2].
   */
  public Term visitSchText(SchText schText)
  {
    SchText oldSchText = schText;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldSchText = schText;
      schText = (SchText) rewriteOnce(manager_, section_, schText, rules_);
      rewrites++;
      if (rewrites > MAX_REWRITES)
        throw new RuntimeException("Infinite loop in rules on schema text "+schText);
    } while (schText != oldSchText);
    // now recurse into subexpressions
    return VisitorUtils.visitTerm(this, schText, true);
  }

  /**
   * Returns a rewritten version of the given schema text by trying to prove
   * <code>schText schemaEquals result</code> using one of the given rules.
   * If the prover fails, the original schema text is returned.
   */
  public static SchText rewriteOnce(SectionManager manager,
                               String section,
                               SchText schText,
                               RuleTable rules)
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerExpr joker = (ProverJokerExpr) factory.createJokerExpr("_");
    // now create the predicate: schText \schemaEquals joker
    System.out.println("Rewriting schtext: "+schText);
    Expr original = factory.createSchExpr(schText);
    TupleExpr pair = factory.createTupleExpr(original, joker);
    Pred pred = factory.createMemPred(pair, schemaEqualsRefExpr_, Boolean.TRUE);
    PredSequent predSequent = factory.createPredSequent();
    predSequent.setPred(pred);
    SimpleProver prover =
      new SimpleProver(rules, manager, section);
    if (prover.prove(predSequent)) {
      Expr newExpr = (Expr) ProverUtils.removeJoker(joker.boundTo());
      if (newExpr instanceof SchExpr) {
        SchText result = ((SchExpr)newExpr).getSchText(); 
        System.out.println("Rewrote to "+result);
        return result;
      }
      else
        throw new RuntimeException("Incorrect schemaEquals rule returned: "+newExpr);
    }
    return schText;
  }

  /**
   * Returns a rewritten version of the given expression by trying to
   * prove <code>expr = JokerExpr</code> using the given rules.  Note
   * that this is not recursive, i.e. the children of the expression
   * are not rewritten.  If the prover fails, the given expression
   * itself is returned.
   */
  public static Term rewriteOnce(SectionManager manager,
                               String section,
                               Expr expr,
                               RuleTable rules)
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerExpr joker = (ProverJokerExpr) factory.createJokerExpr("_");
    Pred pred = factory.createEquality(expr, joker);
    PredSequent predSequent = factory.createPredSequent();
    predSequent.setPred(pred);
    SimpleProver prover =
      new SimpleProver(rules, manager, section);
    if (prover.prove(predSequent)) {
      return ProverUtils.removeJoker(joker.boundTo());
    }
    return expr;
  }

  /**
   * Returns a rewritten version of the given predicate by trying to
   * prove <code>pred \iff JokerPred</code> using the given rules.
   * Note that this is not recursive, i.e. the children of the
   * predicate are not rewritten.  If the prover fails, the given
   * predicate itself is returned.
   */
  public static Term rewriteOnce(SectionManager manager,
                               String section,
                               Pred pred,
                               RuleTable rules)
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerPred joker = (ProverJokerPred) factory.createJokerPred("_");
    PredSequent predSequent = factory.createPredSequent();
    predSequent.setPred(factory.createIffPred(pred, joker));
    SimpleProver prover =
      new SimpleProver(rules, manager, section);
    if (prover.prove(predSequent)) {
      return ProverUtils.removeJoker(joker.boundTo());
    }
    return pred;
  }

  /**
   * Recurses into a Spec or ZSect and rewrites predicates and
   * expressions using the given rules.
   *
   * @throws NullPointerException if term is <code>null</code>.
   */
  public static Term rewrite(SectionManager manager,
                             Term term,
                             RuleTable rules)
  {
    Rewrite visitor = new Rewrite(manager, rules);
    return (Term) term.accept(visitor);
  }

  /**
   * Recurses into a term and rewrites predicates and
   * expressions using the given rules.
   *
   * @throws NullPointerException if term is <code>null</code>.
   */
  public static Term rewrite(SectionManager manager,
                             String section,
                             Term term,
                             RuleTable rules)
  {
    Rewrite visitor = new Rewrite(manager, rules);
    visitor.section_ = section;
    return (Term) term.accept(visitor);
  }
}
