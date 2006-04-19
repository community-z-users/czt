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
import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.util.Factory;

/**
* @author Mark Utting
*
* FlatRangeSet(a,b,s) implements a..b = s.
* However, the a and b bounds are both optional, which allows
* these objects to represent the set of naturals and the set of
* integers etc.
*/
public class FlatRangeSet extends FlatEvalSet
{  
  protected Factory factory_ = new Factory();

  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** The exact value of the lower bound, or null if not known. */
  protected BigInteger lower_;
  
  /** The exact value of the upper bound, or null if not known. */
  protected BigInteger upper_;

  /** The index into args of the lower bound name (-1 if no bound) */
  //@ invariant -1 <= lowerArg_ && lowerArg_ <= 0;
  //@ invariant lower_ != null ==> lowerArg_ != -1;
  private int lowerArg_ = -1;
  
  /** The index into args of the upper bound name (-1 if no bound) */
  //@ invariant -1 <= upperArg_ && upperArg_ <= 1; 
  //@ invariant upper_ != null ==> upperArg_ != -1;
   private int upperArg_ = -1;
   
   /** The index into args of the name of the resulting set */
   //@ invariant 0 <= setArg_ && setArg_ <= 2; 
   private int setArg_ = -1;
    
  /** Creates a FlatRangeSet object, with optional bounds.
   *
   * @param lowerBound  a lower bound expression, or null for no bound.
   * @param upperBound  an upper bound expression, or null for no bound.
   * @param set         the name of the resulting set of integers.
   */
  public FlatRangeSet(ZRefName lowerBound, ZRefName upperBound, ZRefName set)
  {
    args = new ArrayList<ZRefName>();
    if (lowerBound != null) {
      lowerArg_ = args.size();
      args.add(lowerBound);
    }
    if (upperBound != null) {
      upperArg_ = args.size();
      args.add(upperBound);
    }
    setArg_ = args.size();
    args.add(set);
    solutionsReturned = -1;
  }

  /** Saves the Bounds information for later use.
   *  Note that we cannot deduce any constraints on a or b
   *  from a..b.  Not even a<=b, because the b<a case is
   *  allowable (it just means that a..b is empty).
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    return bnds.setEvalSet(args.get(setArg_),this);
  }

  public BigInteger getLower()
  {
    LOG.entering("FlatRangeSet", "getLower");
    BigInteger result = null;
    if (lower_ != null)
      result = lower_;
    else if (lowerArg_ >= 0 && bounds_ != null)
      result = bounds_.getLower(args.get(lowerArg_));
	LOG.exiting("FlatRangeSet", "getLower", result);
    return result;
  }

  public BigInteger getUpper()
  {
    LOG.entering("FlatRangeSet", "getUpper");
	BigInteger result = null;
    if (upper_ != null)
      result = upper_;
    if (upperArg_ >= 0 && bounds_ != null)
      result = bounds_.getUpper(args.get(upperArg_));
	LOG.exiting("FlatRangeSet", "getUpper", result);
    return result;
  }

  public BigInteger maxSize()
  {
	BigInteger low = getLower();
	BigInteger high = getUpper();
	if (low == null || high == null)
	  return null;
	else if(high.compareTo(low)<0)
	  return new BigInteger("0");
	else
	  return high.subtract(low).add(BigInteger.ONE);
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue(args.get(setArg_), this);
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
    ZRefName bound = args.get(boundArg);
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
  
  /** Estimate the size of the set in the given environment. */
  public double estSize(Envir env) {
    lower_ = getBound(env, lowerArg_);
    upper_ = getBound(env, upperArg_);
    return setSize(lower_, upper_);
  }

  public double estSubsetSize(Envir env, ZRefName element)
  {
    assert bounds_ != null;
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

  /** Estimate the size of the set after setMode(). */
  public double estSize()
  {
    assert(evalMode_ != null);
    return estSize(evalMode_.getEnvir());
  }

  private class setIterator implements Iterator<Expr>
  {
    protected BigInteger current_;
    protected BigInteger highest_;
    
    public setIterator(BigInteger low, BigInteger high)
    {
      assert(low != null);
      assert(high != null);
      current_ = low;
      highest_ = high;
    }
    public boolean hasNext()
    {
      return (current_.compareTo(highest_) <= 0);
    }
    public Expr next()
    {
      BigInteger temp = current_;
      current_ = current_.add(BigInteger.ONE);
      return factory_.createNumExpr(temp);
    }
    public void remove()
    {
      throw new UnsupportedOperationException(
          "The Remove Operation is not supported");
    }
  }


  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *
  * @return an Iterator object.
  */
  //@ requires getMode() != null;
  public Iterator<Expr> iterator()
  {
    assert(evalMode_ != null);
    Envir env = evalMode_.getEnvir();
    lower_ = getBound(env, lowerArg_);
    upper_ = getBound(env, upperArg_);
    if (lower_ == null || upper_ == null)
      throw new EvalException("Unbounded integer range "+this);
    return new setIterator(lower_, upper_);
  }

  /** This uses bounds information about element (if any)
   *  to reduce the size of the set that is returned.
   *  The set that is returned is guaranteed to be a subset
   *  (or equal to) the true set of elements in the range. 
   *  This methods has no side-effects, so does not change the
   *  set returned by the usual members() method.
   */
  public Iterator<Expr> subsetIterator(ZRefName element)
  {
    assert evalMode_ != null;
    assert bounds_ != null;
    Envir env = evalMode_.getEnvir();
    BigInteger low = getBound(env, lowerArg_);
    BigInteger high = getBound(env, upperArg_);
    BigInteger elemLow = bounds_.getLower(element);
    BigInteger elemHigh = bounds_.getUpper(element);
    
    if (low != null && elemLow != null)
      low = low.max(elemLow);  // take the tighter of the two bounds.
    else if (lowerArg_ < 0)
      low = elemLow; // real lower bound is infinite, so use elemLow.

    if (high != null && elemHigh != null)
      high = high.min(elemHigh);  // take the tighter of the two bounds.
    else if (upperArg_ < 0)
      high = elemHigh; // real upper bound is infinite, so use elemHigh.

    if (low == null || high == null)
      throw new EvalException("Unbounded integer "+element+" in "+this);
    
    return new setIterator(low, high);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    Envir env = evalMode_.getEnvir();
    boolean result = false;
    lower_ = getBound(env, lowerArg_);
    upper_ = getBound(env, upperArg_);
    ZRefName setName = args.get(setArg_);
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(setArg_)) {
        Expr otherSet = env.lookup(setName);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        env.setValue(setName, this);
        result = true;
      }
    }
    return result;
  }

  /** Tests for membership of the set.
  * @param e  The fully evaluated expression.
  * @return   true iff e is a member of the set.
  */
  //@ requires getMode() != null;
  public boolean contains(Object e)
  {
    assert evalMode_ != null;
    Envir env = evalMode_.getEnvir();
    if ( !(e instanceof NumExpr))
      throw new EvalException("Type error: members of FlatRangeSet must be numbers: " + e);
    BigInteger i = ((NumExpr)e).getValue();
    lower_ = getBound(env, lowerArg_);
    upper_ = getBound(env, upperArg_);
    return (lower_ == null || lower_.compareTo(i) <= 0)
        && (upper_ == null || upper_.compareTo(i) >= 0);
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("FlatRangeSet(");
    if (lowerArg_ < 0)
      result.append("-");
    else
      result.append(args.get(lowerArg_));
    result.append(",");
    if (upperArg_ < 0)
      result.append("-");
    else
      result.append(args.get(upperArg_));
    result.append(",");
    result.append(args.get(setArg_));
    result.append(")");
    return result.toString();
  }
  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatRangeSetVisitor) {
      FlatRangeSetVisitor flatPlusVisitor = (FlatRangeSetVisitor) visitor;
      return flatPlusVisitor.visitFlatRangeSet(this);
    }
    return super.accept(visitor);
  }

  /** This implementation of equals handles two RangeSets efficiently.
   *  In other cases, it uses the equalEvalSet method from FlatPred.
   *  This equals method is really only meant to be used after
   *  the sets have been evaluated.  It is not clear what it does
   *  or should do before that.
   */
  public boolean equals(Object other) {
    if (other instanceof FlatRangeSet) {
      FlatRangeSet rset = (FlatRangeSet)other;
      /* An alternative equality test, which is less elegant.
      // handle the no-bounds at all case.
      if (lower_ == null && upper_ == null) {
        return rset.lower_ == null && rset.upper_ == null;
      }
      // handle the no lower bound case.
      if (lower_ == null) {
        // we know that upper_ != null;
        return rset.lower_ == null
            && rset.upper_ != null
            && upper_.compareTo(rset.upper_) == 0;
      }
      // handle the no upper bound case.
      if (upper_ == null) {
        // we know that lower_ != null;
        return rset.lower_ != null
            && rset.upper_ == null
            && lower_.compareTo(rset.lower_) == 0;
      }
      // now we know that lower_ != null and upper_ != null
      if (rset.lower_ == null || rset.upper_ == null)
        return false;
      // now we know that rset.lower_ != null and rset.upper_ != null
      // handle the empty range case (lower_ > upper_) specially.
      if (lower_.compareTo(upper_)>0) {
        return rset.lower_.compareTo(rset.upper_) > 0;
      }
      return lower_.equals(rset.lower_)
          && upper_.equals(rset.upper_);
      */
      if ((lower_ == null) != (rset.lower_ == null))
        return false;
      if ((upper_ == null) != (rset.upper_ == null))
        return false;
      // handle the empty range case (lower_ > upper_) specially.
      if (lower_ != null && upper_ != null 
          && lower_.compareTo(upper_)>0) {
        return rset.lower_.compareTo(rset.upper_) > 0;
      }
      else
        return (lower_ == null || lower_.equals(rset.lower_))
            && (upper_ == null || upper_.equals(rset.upper_));
    } else if (other instanceof EvalSet) {
      return equalsEvalSet(this,(EvalSet)other);
    } else {
      return false;
    }
  }
}
