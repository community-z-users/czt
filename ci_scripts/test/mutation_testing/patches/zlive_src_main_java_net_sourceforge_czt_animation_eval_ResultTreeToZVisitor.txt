/*
  Copyright (C) 2007 Mark Utting
  This file is part of the CZT project.

  The CZT project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval;

import java.util.Iterator;

import net.sourceforge.czt.animation.eval.result.*;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.LetExprVisitor;

/**
 * This class converts ZLive-specific terms into standard Z AST nodes.
 * It is typically called before printing a term.
 * You can use setEvalSetSize to control how many elements are
 * printed when a large or infinite EvalSet is encountered.
 *
 * @author marku
 *
 */
public class ResultTreeToZVisitor
  implements TermVisitor<Term>,
             EvalSetVisitor<Term>,
	     PowerSetVisitor<Term>,
             ProdSetVisitor<Term>,
             RelSetVisitor<Term>,
             LetExprVisitor<Term>
{
  private Factory factory_ = new Factory();

  /** Stop evaluating elements of a set after this many. */
  private static int evalSetSize = -1;  // infinity

  public ResultTreeToZVisitor()
  {
    VisitorUtils.checkVisitorRules(this);
  }

  public static int getEvalSetSize()
  {
    return evalSetSize;
  }

  /** Set the maximum number of set elements that the printer
   *  will try to display.  If the set contains more elements
   *  that this number, then '...' will be printed for the remaining
   *  elements.  A value of -1 is interpreted as meaning 'infinite'.
   * @param size
   */
  public static void setEvalSetSize(int size)
  {
    evalSetSize = size;
  }

  /** A convenience version of setEvalSetSize that takes a string parameter. */
  public static void setEvalSetSize(String sizeString)
  {
    evalSetSize = Integer.parseInt(sizeString);
  }

  /** Returns a name that represents an unknown number of elements. */
  protected Expr etc()
  {
    return factory_.createRefExpr(factory_.createZName("..."));
  }

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, false);
  }

  public Term visitEvalSet(EvalSet evalSet)
  {
    ZExprList elements = factory_.createZExprList();
    Iterator<Expr> iter = evalSet.iterator();
    int count = 0;
    while (iter.hasNext() && count != evalSetSize) {
      elements.add((Expr) visit(iter.next()));
      count++;
    }
    if (iter.hasNext()) {
      // too many to evaluate, so show that there are still more to come...
      elements.add(etc());
    }
    return factory_.createSetExpr(elements);
  }

  public Term visitPowerSet(PowerSet powerSet)
  {
    Expr baseExpr = (Expr) visit(powerSet.getBaseSet());
    return factory_.createPowerExpr(baseExpr);
  }

  public Term visitProdSet(ProdSet prodSet)
  {
    ZExprList baseSets = factory_.createZExprList();
    for (EvalSet evalSet : prodSet.getBaseSets()) {
      baseSets.add((Expr) visit(evalSet));
    }
    return factory_.createProdExpr(baseSets);
  }

  /** We do not attempt to enumerate function spaces,
   *  since this is rarely useful -- they are usually too big,
   *  and they are usually used for membership tests.
   *  Instead, this returns expressions like: domain op range,
   *  where op is one of the function space operators.
   */
  public Term visitRelSet(RelSet relSet)
  {
    String func = relSet.funcNameUnicode();
    Name funcName = factory_.createZName(ZString.ARG_TOK+func+ZString.ARG_TOK);
    ZExprList args = factory_.createZExprList();
    args.add( (Expr) visit(relSet.getDom()));
    args.add( (Expr) visit(relSet.getRan()));
    return factory_.createRefExpr(funcName, args, true, true);
  }

  /**
   * Convert the strange LET expressions that ZLive uses for
   * function/relation spaces back into normal function/relation spaces.
   * This is useful when we are printing unfolded terms.
   *
   * @param expr
   * @return
   */
  public Term visitLetExpr(LetExpr expr)
  {
    RelSet relset = FlattenVisitor.getRelSet(expr);
    if (relset == null) {
      return expr;
    }
    else {
      return visitRelSet(relset);
    }
  }

  private Term visit(Term t)
  {
    return t.accept(this);
  }
}
