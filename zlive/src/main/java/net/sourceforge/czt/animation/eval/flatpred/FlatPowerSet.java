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
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.result.EvalSet;
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
  /** The value of the base set, if known. */
  private EvalSet<Expr> base_;

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
    base_ = bnds.getEvalSet(args_.get(0));
    return bnds.setEvalSet(getLastArg(),null); // TODO
  }

  /** TODO: extend lower/upper bounds to talk about the elements IN the set? */
  public BigInteger getLower()
  {
    return null;
  }

  public BigInteger getUpper()
  {
    return null;
  }

  /** Maximum size is 2^baseSize, same as size(). */
  public BigInteger maxSize()
  {
    if (base_ != null) {
      BigInteger baseSize = base_.maxSize();
      if (baseSize.doubleValue() < 1000)
        return BigInteger.ONE.shiftLeft(baseSize.intValue());
      else
        throw new EvalException("I do not want to calculate maxSize of powerset bigger than 2^1000");
    }
    return null;
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

  /** This should only be called after nextEvaluation(). */
  public int size()
  {
    assert 0 < solutionsReturned_;
    assert base_ != null;
    BigInteger baseSize = base_.maxSize();
    if (baseSize.doubleValue() < 30)
      // bigger than 2^30 is too big!
      return Integer.MAX_VALUE;
    else {
      return 1 << baseSize.intValue();
    }
  }

  /** Estimate the size of the set in the given environment. */
  public double estSize(Envir env) {
    if (base_ != null)
      return Math.pow(2.0, base_.estSize());
    return EvalSet.UNKNOWN_SIZE;
  }

  /** TODO: see if we can reduce size estimates using cardinality? */
  public double estSubsetSize(Envir env, ZName element)
  {
    return estSize(env);
  }
  
  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    Envir env = evalMode_.getEnvir();
    base_ = (EvalSet) env.lookup(args_.get(0));
    boolean result = false;
    ZName setName = getLastArg();
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      if (evalMode_.isInput(setName)) {
        Expr otherSet = env.lookup(setName);
        result = this.equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        env.setValue(setName, null); // TODO implement PowerSet
        result = true;
      }
    }
    return result;
  }

  protected Expr nextMember()
  {
    throw new RuntimeException("FlatPowerSet does not implement nextMember yet.");
  }

  /** Tests for membership of the set.
  * @param e  The fully evaluated expression.
  * @return   true iff e is a member of the set.
  */
  //@ requires getMode() != null;
  public boolean contains(Object e)
  {
    assert evalMode_ != null;
    assert base_ != null;
    if (e instanceof EvalSet) {
      EvalSet<Expr> set = (EvalSet) e;
      boolean result = true;
      for (Expr elem : set)
        if ( ! base_.contains(elem)) {
          result = false;
          break;
        }
      return result;
    }
    else
      throw new EvalException("Type Error in "+e+" in "+this);
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
