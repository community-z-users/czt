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
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

public class ResultTreeToZVisitor
  implements DiscreteSetVisitor<Term>,
	     PowerSetVisitor<Term>,
	     ProdSetVisitor<Term>
{
  private Factory factory_ = new Factory();

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, false);
  }

  public Term visitDiscreteSet(DiscreteSet discreteSet)
  {
    ZExprList elements = factory_.createZExprList();
    for (Iterator<Expr> iter = discreteSet.iterator(); iter.hasNext();) {
      elements.add((Expr) visit(iter.next()));
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

  private Term visit(Term t)
  {
    return t.accept(this);
  }
}
