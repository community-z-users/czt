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
* FlatDiscreteSet(A,s) implements {Elements of ArrayList A} = s
*/
public class FlatDiscreteSet
extends FlatPred
implements EvalSet
{
  protected Factory factory_ = new Factory();
  protected Set<ZRefName> vars_ = new HashSet<ZRefName>();

  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** Contains the enumerated members of the set. */
  protected Set<Expr> iterateSet_;

  public FlatDiscreteSet(List<ZRefName> elements, ZRefName set)
  {
    Object itNext;
    // remove duplicate ZRefNames
    Set<ZRefName> noDups = new HashSet<ZRefName>(elements);
    args = new ArrayList<ZRefName>(noDups);
    vars_.addAll(noDups);
    args.add(set);
    solutionsReturned = -1;
    iterateSet_ = null;
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
    return bnds.setEvalSet(args.get(args.size()-1), this);
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
    int numElems = args.size()-1;
    if (numElems <= 0)
      return null;
    // calculate min of all the elements (null = -infinity).
    BigInteger result = bounds_.getLower(args.get(0));
    for (int i=1; result != null && i < numElems; i++) {
      BigInteger tmp = bounds_.getLower(args.get(i));
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
    int numElems = args.size()-1;
    if (numElems <= 0)
      return null;
    // calculate max of all the elements (null = infinity).
    BigInteger result = bounds_.getUpper(args.get(0));
    for (int i=1; result != null && i < numElems; i++) {
      BigInteger tmp = bounds_.getUpper(args.get(i));
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
      m.getEnvir().setValue(args.get(args.size()-1), this);
    return m;
  }

  /** The maximum size of the set is the number of distinct expressions.
   */
  public BigInteger maxSize()
  {
	return BigInteger.valueOf(args.size()-1);
  }

  /** Estimate the size of the set. */
  public double estSize(Envir env)
  {
    assert(vars_ != null);
    return ((double)vars_.size());
  }
  
  /** Estimate the size of the set. */
  public double estSize()
  {
    assert(evalMode_ != null);
    return estSize(evalMode_.getEnvir());
  }

  public double estSubsetSize(Envir env, ZRefName elem)
  {
    return estSize(env);
  }
  
  /** A list of all the free variables that this set depends upon.
  * @return The free variables.
  */
  public Set freeVars()
  {
    return vars_;
  }

  /** Iterate through all members of the set.
  *   It guarantees that there will be no duplicates.
  *   Note: this method must only be called AFTER
  *   nextEvaluation(), because all free variables of the
  *   set must be instantiated before we can enumerate the members
  *   of the set.
  *
  * @return an Iterator object.
  */
  public Iterator<Expr> members() {
    assert solutionsReturned > 0;
    if(iterateSet_ == null) {
      iterateSet_ = new HashSet<Expr>();
      Envir env = evalMode_.getEnvir();
      for (ZRefName var : vars_) {
        Expr value = (Expr)env.lookup(var);
        assert value != null;
        iterateSet_.add(value);
      }
    }
    return iterateSet_.iterator();
  }

  public Iterator<Expr> subsetMembers(ZRefName element)
  {
    return members();
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    for (int i=0;i<args.size()-1;i++)
      assert evalMode_.isInput(i);
    boolean result = false;
    ZRefName set = args.get(args.size()-1);
    iterateSet_ = null;
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(args.size()-1)) {
        Expr otherSet = evalMode_.getEnvir().lookup(set);
        result = equals(otherSet);
      } else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue(set, this);
        result = true;
      }
    }
    return result;
  }

  /** Tests for membership of the set.
   *  This can only be called AFTER nextEvaluation().
   *   
   * @param e  The fully evaluated expression.
   * @return   true iff e is a member of the set.
   */
  public boolean isMember(/*@non_null@*/Expr e)
  {
    assert (e != null);
    assert solutionsReturned > 0;
    boolean result = false;
    Iterator<ZRefName> i = vars_.iterator();
    while( ! result && i.hasNext()) {
      Expr value = evalMode_.getEnvir().lookup(i.next());
      if(e.equals(value))
        result = true;
    }
    return result;
  }

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatDiscreteSetVisitor) {
      FlatDiscreteSetVisitor flatDiscreteSetVisitor = (FlatDiscreteSetVisitor) visitor;
      return flatDiscreteSetVisitor.visitFlatDiscreteSet(this);
    }
    return super.accept(visitor);
  }

  /** True iff two EvalSets contain the same elements. */
  public boolean equals(Object otherSet) {
    if (otherSet instanceof EvalSet)
      return equalsEvalSet(this,(EvalSet)otherSet);
    else
      return false;
  }
}
