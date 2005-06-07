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
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
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
 */
public class Rewrite
  implements TermVisitor,
	     ExprVisitor
{
  private List<Rule> rules_;

  private Rewrite(List<Rule> rules)
  {
    rules_ = rules;
  }

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  /**
   * This works fine for expressions, but what to do with
   * other terms like, for example, predicates?
   */
  public Object visitExpr(Expr expr)
  {
    Expr newExpr = (Expr) VisitorUtils.visitTerm(this, expr, true);
    // We assume that newExpr does not contain jokers.
    Factory factory = new Factory(new ProverFactory());
    ProverJokerExpr joker = (ProverJokerExpr) factory.createJokerExpr();
    Pred pred = factory.createEquality(newExpr, joker);
    PredSequent predSequent = factory.createPredSequent();
    predSequent.setPred(pred);
    SimpleProver prover = new SimpleProver(rules_, factory);
    if (prover.prove(predSequent)) {
      // TODO: Copy and remove joker before returning?
      // This should also check whether there are unbound jokers left.
      return joker.getBinding().getExpr().accept(new RemoveJokerVisitor());
    }
    return newExpr;
  }

  /**
   * Rewrites a term using a given rule.
   * Assumes that the conclusion of the rule is an equality.
   *
   * @throws NullPointerExcpetion if term is <code>null</code>.
   */
  public static Term rewrite(Term term, List<Rule> rules)
  {
    Rewrite visitor = new Rewrite(rules);
    return (Term) term.accept(visitor);
  }
}

class RemoveJokerVisitor
  implements TermVisitor
{
  public Object visitTerm(Term term)
  {
    if (term instanceof Joker) {
      Joker joker = (Joker) term;
      Term boundTo = joker.boundTo();
      if (boundTo == null) {
        throw new UnboundJokerException();
      }
      return boundTo;
    }
    return VisitorUtils.visitTerm(this, term, true);
  }
}

class UnboundJokerException
  extends RuntimeException
{
}
