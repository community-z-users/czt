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
import net.sourceforge.czt.zpatt.util.*;
import net.sourceforge.czt.zpatt.visitor.*;

public class Rewrite
  implements TermVisitor,
	     ExprVisitor
{
  private Factory factory_ = new Factory();
  private Rule rule_;

  private Rewrite(Rule rule)
  {
    rule_ = rule;
  }

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  /**
   * This works fine for expressions, but what to do with
   * other terms?
   *
   * @czt.todo Do the proof!
   */
  public Object visitExpr(Expr expr)
  {
    Expr newExpr = (Expr) VisitorUtils.visitTerm(this, expr, true);
    JokerExpr joker = factory_.createJokerExpr();
    Pred pred = factory_.createEquality(newExpr, joker);
    Deduction deduction =
      new DeductionImpl(rule_, factory_.createPredSequent(null, pred));
    if (deduction.isValid()) {
      // Copy and remove joker before returning?
      // This should also check whether there are unbound joker left.
      return joker.getBinding();
    }
    return newExpr;
  }

  /**
   * Rewrites a term using a given rule.
   * Assumes that the conclusion of the rule is an equality.
   */
  public static Term rewrite(Term term, Rule rule)
  {
    Rewrite visitor = new Rewrite(rule);
    return (Term) term.accept(visitor);
  }

  public static Rule getTestRule()
  {
    Factory factory = new Factory();
    Pred equality = factory.createEquality(
      factory.createRefExpr(factory.createRefName("BirthdayBook")),
      factory.createRefExpr(factory.createRefName("Uhhhhhhhhhhh")));
    Rule rule = factory.createRule();
    rule.getSequent().add(factory.createPredSequent(null, equality));
    return rule;
  }
}
