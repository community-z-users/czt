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
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.util.Factory;

/**
* @author Mark Utting
*
* FlatDiscreteSet(A,s) implements {Elements of ArrayList A} = s
*/
public class FlatDiscreteSet extends FlatEvalSet
{
  protected Factory factory_ = new Factory();

  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** The number of expressions returned by nextMember() */
  private int membersReturned;

  public FlatDiscreteSet(List<ZRefName> elements, ZRefName set)
  {
    // remove duplicate ZRefNames
    Set<ZRefName> noDups = new HashSet<ZRefName>(elements);
    args_ = new ArrayList<ZRefName>(noDups);
    args_.add(set);
    solutionsReturned_ = -1;
  }

  //@ requires newargs.size() >= 1;
  public FlatDiscreteSet(List<ZRefName> newargs)
  {
    this(newargs.subList(0,newargs.size()-1),
        newargs.get(newargs.size()-1));
  }

  /** Saves the Bounds information for later use.
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    return bnds.setEvalSet(args_.get(args_.size()-1), this);
  }

  /** Calculates minimum of the lower bounds of all the elements.
   *  Returns null if the set does not contain integers,
   *  or if it is empty, or if some of the elements do not
   *  have any lower bound.
   */
  public BigInteger getLower()
  {
    if (bounds_ == null)
      return null;
    int numElems = args_.size()-1;
    if (numElems <= 0)
      return null;
    // calculate min of all the elements (null = -infinity).
    BigInteger result = bounds_.getLower(args_.get(0));
    for (int i=1; result != null && i < numElems; i++) {
      BigInteger tmp = bounds_.getLower(args_.get(i));
      if (tmp == null)
	result = tmp;
      else
	result = result.min(tmp);
    }
    return result;
  }

  /** Calculates maximum of the upper bounds of all the elements.
   *  Returns null if the set does not contain integers,
   *  or if it is empty, or if some of the elements do not
   *  have any upper bound.
   */
  public BigInteger getUpper()
  {
    if (bounds_ == null)
      return null;
    int numElems = args_.size()-1;
    if (numElems <= 0)
      return null;
    // calculate max of all the elements (null = infinity).
    BigInteger result = bounds_.getUpper(args_.get(0));
    for (int i=1; result != null && i < numElems; i++) {
      BigInteger tmp = bounds_.getUpper(args_.get(i));
      if (tmp == null)
	result = tmp;
      else
	result = result.max(tmp);
    }
    return result;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeFunction(env);
    // bind (set |-> this), so that size estimates work better.
    if (m != null)
      m.getEnvir().setValue(args_.get(args_.size()-1), this);
    return m;
  }

  /** The maximum size of the set is the number of distinct expressions.
   */
  public BigInteger maxSize()
  {
    return BigInteger.valueOf(args_.size()-1);
  }

  /** Estimate the size of the set. */
  public double estSize(Envir env)
  {
    return (double) (args_.size() - 1);
  }

  /** For FlatDiscreteSet, the estSubsetSize is the same as estSize. */
  public double estSubsetSize(Envir env, ZRefName elem)
  {
    return estSize(env);
  }

  /** For FlatDiscreteSet, subsetMembers(...) is the same as members(). */
  public Iterator<Expr> subsetIterator(ZRefName element)
  {
    return iterator();
  }

  /** Does the actual evaluation. */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    boolean result = false;
    ZRefName set = args_.get(args_.size()-1);
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      resetResult();
      if (evalMode_.isInput(getLastArg())) {
        Expr otherSet = evalMode_.getEnvir().lookup(set);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(set, this);
        result = true;
      }
    }
    membersReturned = 0;
    return result;
  }

  protected Expr nextMember()
  {
    assert solutionsReturned_ > 0;
    int numExprs = args_.size() - 1;
    if (membersReturned == numExprs)
      return null;
    Envir env = evalMode_.getEnvir();
    ZRefName var = args_.get(membersReturned);
    Expr result = env.lookup(var);
    membersReturned++;
    return result;
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatDiscreteSetVisitor)
      return ((FlatDiscreteSetVisitor<R>) visitor).visitFlatDiscreteSet(this);
    else
      return super.accept(visitor);
  }

  /** True iff two EvalSets contain the same elements. */
  public boolean equals(Object otherSet) {
      return equalsEvalSet(this,otherSet);
  }
}
