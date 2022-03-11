/**
 Copyright (C) 2004 Mark Utting
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

import java.math.BigInteger;
import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatCardVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Mark Utting
 *
 * FlatCard(A,s) implements # A = s
 */
public class FlatCard extends FlatPred
{
  protected Factory factory_ = new Factory();

  public FlatCard(ZName set, ZName size)
  {
    args_ = new ArrayList<ZName>(2);
    args_.add(set);
    args_.add(size);
    solutionsReturned_ = -1;
  }

  public boolean inferBounds(Bounds bnds)
  {
    boolean changed = false;
    ZName setName = args_.get(0);
    ZName sizeName = args_.get(1);
    EvalSet set = bnds.getEvalSet(setName);
    if (set != null) {
      BigInteger maxSize = set.maxSize();
      if (maxSize != null)
        changed |= bnds.addUpper(sizeName, maxSize);
    }
    changed |= bnds.addLower(sizeName, new BigInteger("0"));
    return changed;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/Envir env)
  {
    return modeFunction(env);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    assert evalMode_.isInput(args_.get(0));
    boolean result = false;
    ZName setName = args_.get(0);
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      EvalSet set = (EvalSet) evalMode_.getEnvir().lookup(setName);
      int setSize = set.size();
      // TODO: allow sets to return BigInteger sizes.
      if (setSize == Integer.MAX_VALUE) {
        throw new EvalException("cardinalities larger than "+setSize+" not handled yet");
      }
      Expr size = factory_.createNumExpr(setSize);
      if (evalMode_.isInput(args_.get(1))) {
        Expr thisSize = evalMode_.getEnvir().lookup(args_.get(1));
        if (thisSize.equals(size))
          result = true;
      }
      else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(args_.get(1), size);
        result = true;
      }
    }
    return result;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.eval.flatpred.FlatPred#toString()
   */
  @Override
  public String toString()
  {
    return "# "+printArg(0)+" = "+printArg(1);
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatCardVisitor) {
      return ((FlatCardVisitor<R>) visitor).visitFlatCard(this);
    }
    return super.accept(visitor);
  }
}
