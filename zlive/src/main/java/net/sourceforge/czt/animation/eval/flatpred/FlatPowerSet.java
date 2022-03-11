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
import java.util.Iterator;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatPowerSetVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.animation.eval.result.PowerSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
* @author Mark Utting
*
* FlatPowerSet(base,set) implements \power base = set.
* It is capable of checking that a given finite set is a member of
* the powerset (it does this by iterating through its elements)
* and of generating all elements of the powerset when the
* base set is small (<= 30).
*/
public class FlatPowerSet extends FlatPred
{
  /** Creates a FlatPowerSet object.
   *
   * @param baseSet  the underlying set, from which all subsets will be taken.
   * @param set      the name of the resulting set of subsets.
   */
  public FlatPowerSet(ZName baseSet, ZName set)
  {
    args_ = new ArrayList<ZName>();
    args_.add(baseSet);
    args_.add(set);
    solutionsReturned_ = -1;
  }

  /** Adds this power set into the Bounds information.
   */
  public boolean inferBounds(Bounds bnds)
  {
    EvalSet base = bnds.getEvalSet(args_.get(0));
    FuzzySet fuzzy = null;
    if (base != null) {
      BigInteger basesize = base.maxSize();
      BigInteger size = null;
      double estsize = Math.pow(2.0, base.estSize());
      // we treat sets bigger that 2^1000 as being infinite,
      // to avoid wasting time calculating huge BigInteger values.
      if (basesize != null &&
          basesize.compareTo(BigInteger.valueOf(1000)) < 0)
          size = BigInteger.valueOf(2).pow(basesize.intValue());
      if (size != null || estsize < EvalSet.INFINITE_SIZE)
        fuzzy = new FuzzySet(getLastArg().toString(), estsize, size);
    }
    if (fuzzy == null)
      return false;
    else
      return bnds.setEvalSet(getLastArg(),fuzzy);
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue(getLastArg(), null); // TODO
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
      EvalSet base = (EvalSet) env.lookup(args_.get(0));
      EvalSet powerSet = new PowerSet(base);
      if (evalMode_.isInput(setName)) {
        Expr otherSet = env.lookup(setName);
        result = powerSet.equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        env.setValue(setName, powerSet);
        result = true;
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printArg(1) + " = " + "P "+printArg(0);
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatPowerSetVisitor)
      return ((FlatPowerSetVisitor<R>) visitor).visitFlatPowerSet(this);
    else
      return super.accept(visitor);
  }

  public Iterator<Expr> subsetIterator(ZName element)
  {
    // TODO Auto-generated method stub
    return null;
  }
}
