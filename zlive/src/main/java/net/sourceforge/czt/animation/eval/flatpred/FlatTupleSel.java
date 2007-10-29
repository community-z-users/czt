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

import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatTupleSelVisitor;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZName;

/** FlatTupleSel implements the tuple.i = result predicate.
 *  The index i can range from 1 up to the length of the tuple.
 */
public class FlatTupleSel extends FlatPred
{
  private Integer selection_;

  public FlatTupleSel(ZName tuple, Integer i, ZName result)
  {
    if (i <= 0)
      throw new CztException("Illegal tuple selection index: " + i);
    selection_ = i;
    args_ = new ArrayList<ZName>(2);
    args_.add(tuple);
    args_.add(result);
    solutionsReturned_ = -1;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.eval.flatpred.FlatPred#inferBounds(net.sourceforge.czt.animation.eval.flatpred.Bounds)
   */
  @Override
  public boolean inferBounds(Bounds bnds)
  {
    bnds.addStructureArg(args_.get(0),
        Integer.valueOf(selection_),
        args_.get(1));
    return false;
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
    assert(solutionsReturned_ >= 0);
    boolean result = false;
    if(solutionsReturned_ == 0) {
      solutionsReturned_++;
      if (evalMode_.isInput(0)) {
        Expr expr = evalMode_.getEnvir().lookup(args_.get(0));
        if ( ! (expr instanceof TupleExpr))
          throw new EvalException("Tuple selection cannot handle non-tuple: " + expr);
        TupleExpr tuple = (TupleExpr) expr;
        int size = tuple.getZExprList().size();
        if (size < selection_)
          throw new CztException("Badly typed tuple selection: " + size);
        Expr selected = tuple.getZExprList().get(selection_ - 1);

        if (evalMode_.isInput(1)) {
          // Now check selected against the output
          Expr output = evalMode_.getEnvir().lookup(args_.get(1));
          result = output.equals(selected);
        }
        else {
          // Now assign selected to the result
          evalMode_.getEnvir().setValue(args_.get(1), selected);
          result = true;
        }
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printLastArg() + " = " + printArg(0) + "." + selection_;
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatTupleSelVisitor)
      return ((FlatTupleSelVisitor<R>) visitor).visitFlatTupleSel(this);
    else
      return super.accept(visitor);
  }
}
