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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatDiscreteSetVisitor;
import net.sourceforge.czt.animation.eval.result.DiscreteSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
* @author Mark Utting
*
* FlatDiscreteSet(A,s) implements {Elements of ArrayList A} = s
*/
public class FlatDiscreteSet extends FlatPred
{
  protected Factory factory_ = new Factory();

  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  public FlatDiscreteSet(List<ZName> elements, ZName set)
  {
    // remove duplicate ZNames
    Set<ZName> noDups = new HashSet<ZName>(elements);
    args_ = new ArrayList<ZName>(noDups);
    args_.add(set);
    solutionsReturned_ = -1;
  }

  //@ requires newargs.size() >= 1;
  public FlatDiscreteSet(List<ZName> newargs)
  {
    this(newargs.subList(0,newargs.size()-1),
        newargs.get(newargs.size()-1));
  }

  /** Saves the Bounds information for later use.
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    int numElems = args_.size()-1;
    FuzzySet fuzzy = new FuzzySet(getLastArg().toString(), numElems, BigInteger.valueOf(numElems));
    // now find max and max of the bounds of the elements (null=infinity)
    BigInteger lo = null;
    BigInteger hi = null;
    if (numElems > 0) {
      lo = bounds_.getLower(args_.get(0));
      hi = bounds_.getUpper(args_.get(0));
      for (int i=1; (lo != null || hi != null) && i < numElems; i++) {
        BigInteger tmp = bounds_.getLower(args_.get(i));
        lo = (tmp == null) ? null : lo.min(tmp);
        tmp = bounds_.getUpper(args_.get(i));
        hi = (tmp == null) ? null : hi.max(tmp);
      }
    }
    fuzzy.setLower(lo);
    fuzzy.setUpper(hi);
    return bnds.setEvalSet(getLastArg(), fuzzy);
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    assert bounds_ != null; // inferBounds should have been called.
    Mode m = modeFunction(env);
    return m;
  }

  /** Does the actual evaluation. */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    boolean result = false;
    ZName set = getLastArg();
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      Envir env = evalMode_.getEnvir();
      DiscreteSet newset = new DiscreteSet();
      for (ZName name : args_) {
        if (name != getLastArg())
          newset.add(env.lookup(name));
      }
      if (evalMode_.isInput(getLastArg())) {
        Expr otherSet = evalMode_.getEnvir().lookup(set);
        result = newset.equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(set, newset);
        result = true;
      }
    }
    return result;
  }

 
  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(printLastArg());
    result.append(" = { ");
    for (int i=0; i < args_.size() - 1; i++) {
      result.append(printArg(i));
      if (i < args_.size() - 2)
        result.append(", ");
    }
    result.append(" }");
    return result.toString();
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatDiscreteSetVisitor)
      return ((FlatDiscreteSetVisitor<R>) visitor).visitFlatDiscreteSet(this);
    else
      return super.accept(visitor);
  }
}
