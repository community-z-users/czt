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

import java.util.*;
import java.math.*;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.TermAImpl;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;

/**
* @author Mark Utting
*
* FlatRangeSet(a,b,s) implements a..b = s
*/
public class FlatRangeSet
  extends FlatPred
  implements EvalSet
{
  protected Factory factory_ = new Factory();
  public final double DEFAULT_SIZE = 1000000.0;
  protected BigInteger lower_;
  protected BigInteger upper_;

  public FlatRangeSet(ZRefName lowerBound, ZRefName upperBound, ZRefName set)
  {
    args = new ArrayList();
	args.add(lowerBound);
    args.add(upperBound);
    args.add(set);
    solutionsReturned = -1;
  }

  //@ requires newargs.size() == 3;
  public FlatRangeSet(ArrayList newargs)
  {
    if (newargs == null || newargs.size() != 3)
      throw new IllegalArgumentException("FlatRangeSet requires 3 args");
    args = newargs;
    solutionsReturned = -1;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue(args.get(args.size()-1), this);
    return m;
  }

  /** Looks in the envir (if any) for any upper/lower bounds. */
  private BigInteger getBound(Envir env, ZRefName bound)
  {
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

  public double estSize(Envir env) {
    lower_ = getBound(env, args.get(0));
    upper_ = getBound(env, args.get(1));
    if (lower_ == null || upper_ == null)
      return DEFAULT_SIZE;
    if(upper_.compareTo(lower_)<0)
      return 0.0;
    else
      return (upper_.subtract(lower_).add(BigInteger.ONE).doubleValue());
  }

  /** Estimate the size of the set. */
  public double estSize()
  {
    assert(evalMode_ != null);
    return estSize(evalMode_.getEnvir());
  }
  
  /** A list of all the free variables that this set depends upon.
  * @return The free variables.
  */
  public Set freeVars()
  {
    Set temp = new HashSet(args);
    temp.remove(args.get(args.size()-1));
    return temp;
  }

  private class setIterator implements Iterator
  {
    protected BigInteger current_;
    public setIterator()
    {
      assert(lower_ != null);
      current_ = lower_;
    }
    public boolean hasNext()
    {
      return (current_.compareTo(upper_) <= 0);
 	}
    public Object next()
    {
      BigInteger temp = current_;
      current_ = current_.add(BigInteger.ONE);
      return factory_.createNumExpr(temp);
    }
    public void remove()
	{
	  throw new UnsupportedOperationException("The Remove Operation is not supported");
	}
  }


  /** Iterate through all members of the set.
  *  It guarantees that there will be no duplicates.
  *
  * @return an Iterator object.
  */
  //@ requires getMode() != null;
  public Iterator members()
  {
    assert(evalMode_ != null);
    Envir env = evalMode_.getEnvir();
    lower_ = getBound(env, args.get(0));
    upper_ = getBound(env, args.get(1));
    return (new setIterator());
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    assert evalMode_.isInput(0);
    assert evalMode_.isInput(1);
    Envir env = evalMode_.getEnvir();
    boolean result = false;
    lower_ = getBound(env, args.get(0));
    upper_ = getBound(env, args.get(1));
    ZRefName set = args.get(2);
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(2)) {
        Expr otherSet = env.lookup(set);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        env.setValue(set, this);
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
  public boolean isMember(Expr e)
  {
    assert evalMode_ != null;
    Envir env = evalMode_.getEnvir();
    if ( !(e instanceof NumExpr))
      throw new EvalException("Type error: members of FlatRangeSet must be numbers: " + e);
    BigInteger i = ((NumExpr)e).getValue();
    lower_ = getBound(env, args.get(0));
    upper_ = getBound(env, args.get(1));
    return ((lower_.compareTo(i) <= 0) && (upper_.compareTo(i) >= 0));
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
   */
  public boolean equals(Object other) {
    if (other instanceof FlatRangeSet) {
      FlatRangeSet rset = (FlatRangeSet)other;
      if ((lower_.compareTo(upper_)>0) && ((rset.lower_).compareTo(rset.upper_)>0))
        return true;
      else
        return lower_.equals(rset.lower_) && upper_.equals(rset.upper_);
    } else if (other instanceof EvalSet) {
      return equalsEvalSet(this,(EvalSet)other);
    } else {
      return false;
    }
  }
}
