/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2005 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import java.util.List;
import java.util.ArrayList;
import java.math.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatTupleSel implements the a+b=c predicate. */
public class FlatTupleSel extends FlatPred
{
  private Factory factory_ = new Factory();
  private Integer selection;

  public FlatTupleSel(ZRefName tuple, Integer i, ZRefName result)
  {
    if (i <= 0)
      throw new CztException("Illegal tuple selection index: " + i);
    selection = i;
    args = new ArrayList(2);
    args.add(tuple);
    args.add(result);
    solutionsReturned = -1;
  }
  
  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return modeFunction(env);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  throws EvalException
  {
    assert(evalMode_ != null);
    assert(solutionsReturned >= 0);
    boolean result = false;
    if(solutionsReturned == 0) {
      solutionsReturned++;
      if (evalMode_.isInput(0)) {
        Expr expr = evalMode_.getEnvir().lookup(args.get(0));
	if ( ! (expr instanceof TupleExpr))
	  throw new EvalException("Tuple selection cannot handle non-tuple: " + expr);
	TupleExpr tuple = (TupleExpr) expr;
	int size = tuple.getExpr().size();
	if (size < selection)
	  throw new CztException("Badly typed tuple selection: " + size);
	Expr selected = tuple.getExpr().get(selection - 1);

	if (evalMode_.isInput(1)) {
	  // Now check selected against the output
	  Expr output = evalMode_.getEnvir().lookup(args.get(1));
	  result = output.equals(selected);
	}
	else {
	  // Now assign selected to the result
          evalMode_.getEnvir().setValue(args.get(1), selected);
          result = true;
        }
      }
    }
    return result;
  }
  

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatTupleSelVisitor) {
      FlatTupleSelVisitor flatPlusVisitor = (FlatTupleSelVisitor) visitor;
      return flatPlusVisitor.visitFlatTupleSel(this);
    }
    return super.accept(visitor);
  }
}
