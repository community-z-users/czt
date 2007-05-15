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
import net.sourceforge.czt.animation.eval.flatvisitor.FlatRangeSetVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
* @author Mark Utting
*
* FlatRangeSet(a,b,s) implements a..b = s.
* However, the a and b bounds are both optional, which allows
* these objects to represent the set of naturals and the set of
* integers etc.
*/
public class FlatRangeSet extends FlatPred
{
  /** The average expected size of a closed range a..b */
  private static int averageClosedRange_ = 100;

  protected Factory factory_ = new Factory();

  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** The index into args of the lower bound name (-1 if no bound) */
  //@ invariant -1 <= lowerArg_ && lowerArg_ <= 0;
  private int lowerArg_ = -1;

  /** The index into args of the upper bound name (-1 if no bound) */
  //@ invariant upperArg_ == -1 || upperArg_ == lowerArg__ + 1;
   private int upperArg_ = -1;

   /** The index into args of the name of the resulting set */
   //@ invariant setArg_ == Math.max(lowerArg_, upperArg_) + 1;
   private int setArg_;

  /** Creates a FlatRangeSet object, with optional bounds.
   *
   * @param lowerBound  a lower bound expression, or null for no bound.
   * @param upperBound  an upper bound expression, or null for no bound.
   * @param set         the name of the resulting set of integers.
   */
  public FlatRangeSet(ZName lowerBound, ZName upperBound, ZName set)
  {
    args_ = new ArrayList<ZName>();
    if (lowerBound != null) {
      lowerArg_ = args_.size();
      args_.add(lowerBound);
    }
    if (upperBound != null) {
      upperArg_ = args_.size();
      args_.add(upperBound);
    }
    setArg_ = args_.size();
    args_.add(set);
    solutionsReturned_ = -1;
  }

  /**
   * @return the average expected size of a closed range a..b
   */
  public static int getAverageClosedRange()
  {
    return averageClosedRange_;
  }

  /**
   * Sets the average expected size of a closed range a..b.
   * This is used to guess the best evaluation order during mode analysis.
   * @param averageClosedRange should be 2..1000000000.
   */
  public static void setAverageClosedRange_(int size)
  {
    FlatRangeSet.averageClosedRange_ = size;
  }

  /** Saves the Bounds information for later use.
   *  Note that we cannot deduce any constraints on a or b
   *  from a..b.  Not even a<=b, because the b<a case is
   *  allowable (it just means that a..b is empty).
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    BigInteger lo = null;
    BigInteger up = null;
    if (lowerArg_ >= 0)
      lo = bnds.getLower(args_.get(lowerArg_));
    if (upperArg_ >= 0)
      up = bnds.getUpper(args_.get(upperArg_));

    EvalSet estimate = new RangeSet(lo,up);
    if (estimate.maxSize() == null
        && lowerArg_ >= 0
        && upperArg_ >= 0) {
      // it will be a finite range at evaltime, so we guess its size.
      FuzzySet fuzzy = new FuzzySet(getLastArg().toString(),
          averageClosedRange_, null);
      fuzzy.setLower(lo);
      fuzzy.setUpper(up);
      estimate = fuzzy;
    }
    return bnds.setEvalSet(args_.get(setArg_), estimate);
  }

  public BigInteger getBound(int which)
  {
    BigInteger result = null;
    if (which >= 0 && bounds_ != null)
      result = bounds_.getLower(args_.get(lowerArg_));
    return result;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  @Override public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    assert bounds_ != null;
    Mode m = modeFunction(env);
    return m;
  }

  /** Looks in the envir (if any) for an upper/lower bound.
   *  If boundArg==-1, this means no bound, so the result will be null.
   *  A null result also happens when env==null or the bound is
   *  not yet available in env.
   *
   *  @param env       the (optional) environment to look for bounds in.
   *  @param boundArg  an index into args (ie. lowerArg_ or upperArg_).
   */
  private BigInteger getBound(Envir env, int boundArg)
  {
    if (boundArg < 0)
      return null;
    ZName bound = args_.get(boundArg);
    BigInteger result = null;
    Expr e = null;
    if (env != null)
      e = env.lookup(bound);
    if (e != null) {
      if (!(e instanceof NumExpr))
        throw new EvalException("Non-numeric bound " + bound.getWord() + " = " + e);
      result = ((NumExpr)e).getValue();
    }
    return result;
  }

 /* public BigInteger getLower()
  {
	lower_ = getBound(lBound_);
	return lower_;
  }

  public BigInteger getUpper()
  {
	upper_ = getBound(uBound_);
	return upper_;
  }
*/

  /** Auxiliary function for calculating the size of the range set.
   *  @param low  Bottom of the range, or null if no limit.
   *  @param high Top of the range, or null if no limit.
   *  @return     The number of elements in the set.
   */
  private double setSize(BigInteger low, BigInteger high)
  {
    if (low == null || high == null)
      return Double.POSITIVE_INFINITY;
    if(high.compareTo(low)<0)
      return 0.0;
    else
      return (high.subtract(low).add(BigInteger.ONE).doubleValue());
  }

  /** Estimate the size of the set in the given environment.
   *  TODO: could delete this???
   */
  public double estSize(Envir env)
  {
    return setSize(getBound(env, lowerArg_), getBound(env, upperArg_));
  }

  /** TODO: could delete this???
   */
  public double estSubsetSize(Envir env, ZName element)
  {
    assert bounds_ != null; // inferBounds should have been called.
    BigInteger low = getBound(env, lowerArg_);
    BigInteger high = getBound(env, upperArg_);
    BigInteger elemLow = bounds_.getLower(element);
    BigInteger elemHigh = bounds_.getUpper(element);

    if (low == null) {
      low = elemLow;
    }
    else if (elemLow != null)
      low = low.max(elemLow);

    if (high == null) {
      high = elemHigh;
    }
    else if (elemHigh != null)
      high = high.min(elemHigh);

    return setSize(low, high);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    Envir env = evalMode_.getEnvir();
    boolean result = false;
    if(solutionsReturned_==0) {
      solutionsReturned_++;
      BigInteger lo = getBound(env, lowerArg_);
      BigInteger up = getBound(env, upperArg_);
      RangeSet range = new RangeSet(lo, up);
      ZName setName = args_.get(setArg_);
      if (evalMode_.isInput(setArg_)) {
        Expr otherSet = env.lookup(setName);
        result = range.equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        env.setValue(setName, range);
        result = true;
      }
    }
    return result;
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(printArg(lowerArg_));
    result.append(" .. ");
    result.append(printArg(upperArg_));
    result.append(" = ");
    result.append(printArg(setArg_));
    EvalSet range = null;
    if (bounds_ != null)
      range = bounds_.getEvalSet(args_.get(setArg_));
    if (range != null) {
      result.append(" :: ");
      result.append(range.toString());
    }
    return result.toString();
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatRangeSetVisitor)
      return ((FlatRangeSetVisitor<R>) visitor).visitFlatRangeSet(this);
    else
      return super.accept(visitor);
  }
}
