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

import java.util.Map;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.jaxb.*;
import net.sourceforge.czt.zpatt.util.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * <p>A rewrite engine for Z terms.</p>
 *
 * <p>Given a set or rules and a term (AST), this engine rewrites the
 * term using the rules.</p>
 *
 * Questions:
 * <ul>
 *   <li>First rewrite the children of a term and then try to rewrite
 *     the new term or the other way round?</li>
 *   <li>What happens if two rules can be applied?</li>
 * </ul>
 *
 * @author Petra Malik
 */
public class Rewrite
  implements TermVisitor,
             ExprVisitor,
             PredVisitor,
             ZSectVisitor
{
  private SectionManager manager_;

  private RuleTable rules_;

  private String section_;

  public Rewrite(SectionManager manager, RuleTable rules)
  {
    manager_ = manager;
    rules_ = rules;
  }

  public Object visitZSect(ZSect zSect)
  {
    section_ = zSect.getName();
    return VisitorUtils.visitTerm(this, zSect, true);
  }

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Object visitExpr(Expr expr)
  {
    Expr newExpr = (Expr) VisitorUtils.visitTerm(this, expr, true);
    return rewrite(manager_, section_, newExpr, rules_);
  }

  public Object visitPred(Pred pred)
  {
    Pred newPred = (Pred) VisitorUtils.visitTerm(this, pred, true);
    return rewrite(manager_, section_, newPred, rules_);
  }

  /**
   * Returns a rewritten version of the given expression by trying to
   * prove <code>expr = JokerExpr</code> using the given rules.  Note
   * that this is not recursive, i.e. the children of the expression
   * are not rewritten.  If the prover fails, the given expression
   * itself is returned.
   */
  public static Object rewrite(SectionManager manager,
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
  public static Object rewrite(SectionManager manager,
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
   * @throws NullPointerExcpetion if term is <code>null</code>.
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
   * @throws NullPointerExcpetion if term is <code>null</code>.
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
