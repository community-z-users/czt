/**
Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatRelSetVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.RelSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

public class FlatRelSet
  extends FlatPred
{
  private boolean function_;
  private boolean total_;
  private boolean onto_;
  private boolean injective_;

  public FlatRelSet(ZName baseSet1, ZName baseSet2,
                    boolean function, boolean total,
                    boolean onto, boolean injective,
                    ZName set)
  {
    function_ = function;
    total_ = total;
    onto_ = onto;
    injective_ = injective;
    args_ = new ArrayList<ZName>();
    args_.add(baseSet1);
    args_.add(baseSet2);
    args_.add(set);
    solutionsReturned_ = -1;
  }

  /** Adds this power set into the Bounds information.
   */
  public boolean inferBounds(Bounds bnds)
  {
    return false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeFunction(env);
    return m;
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    Envir env = evalMode_.getEnvir();
    boolean result = false;
    ZName setName = getLastArg();
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      EvalSet base1 = (EvalSet) env.lookup(args_.get(0));
      EvalSet base2 = (EvalSet) env.lookup(args_.get(1));
      RelSet relSet =
        new RelSet(base1, base2, function_, total_, onto_, injective_);
      if (evalMode_.isInput(setName)) {
        Expr otherSet = env.lookup(setName);
        result = relSet.equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        env.setValue(setName, relSet);
        result = true;
      }
    }
    return result;
  }

  /** This returns the function operator, in email markup. */
  public String funcName()
  {
    return RelSet.funcName(function_, injective_, total_, onto_);
  }

  @Override
  public String toString()
  {
    return printLastArg() + " = "
      + printArg(0) + " " + funcName() + " " + printArg(1);
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatRelSetVisitor)
      return ((FlatRelSetVisitor<R>) visitor).visitFlatRelSet(this);
    else
      return super.accept(visitor);
  }
}
