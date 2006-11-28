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
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
* @author Mark Utting
*
* FlatMember(s,e) implements e \in s, where s can be any kind of
* set that implements the EvalSet interface.
*/
public class FlatMember extends FlatPred
{
  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** This is non_null during evaluation */
  protected EvalSet set_;

  /** This is for iterating through set_ */
  protected Iterator current_;

  /** Membership of a set.
   *
   * @param set      Must evaluate to an EvalSet object.
   * @param element  The member of the set.
   */
  public FlatMember(ZName set, ZName element)
  {
    args_ = new ArrayList<ZName>(2);
    args_.add(set);
    args_.add(element);
    solutionsReturned_ = -1;
  }

  public boolean inferBounds(Bounds bnds)
  {
	LOG.entering("FlatMember", "inferBounds", bnds);
	ZName setName = args_.get(0);
	ZName elemName = args_.get(1);
	EvalSet set = bnds.getEvalSet(setName);
	boolean changed = false;
	if (set != null) {
      BigInteger lo = set.getLower();
      if (lo != null)
	    changed |= bnds.addLower(elemName, lo);
      BigInteger hi = set.getUpper();
	  if (hi != null)
		changed |= bnds.addUpper(elemName, hi);
	}
    bounds_ = bnds;
	LOG.exiting("FlatMember", "inferBounds", changed);
	return changed;
  }

  public Mode chooseMode(Envir env)
  {
    // the set must be defined in env.
    ZName setName = args_.get(0);
    ZName elemName = args_.get(1);
    Mode result = new Mode(this, env, args_, Mode.MAYBE_ONE_SOLUTION);
    // is the set an input?
    if (result.isInput(setName)) {
      if (result.isOutput(elemName)) {
        // We will have to generate all members.
        // the actual EvalSet object will be available at evaluation
        // time, but we check to see if it is already available.
        // If it is, we can get better estimates.
        Expr e = env.lookup(setName);
        if (e != null && e instanceof EvalSet)
          result.setSolutions(((EvalSet)e).estSubsetSize(env, elemName));
        else
          result.setSolutions(Double.POSITIVE_INFINITY);
      }
    }
    else {
      result = null;
    }
    return result;
  }

  public void startEvaluation()
  {
    super.startEvaluation();
    assert solutionsReturned_ == 0;
    set_ = (EvalSet)evalMode_.getEnvir().lookup(args_.get(0));
    assert(set_ != null);
  }

  public boolean nextEvaluation() {
    assert evalMode_ != null;
    assert solutionsReturned_ >= 0;
    assert set_ != null;
    boolean result = false;
    ZName element = args_.get(1);
    if (evalMode_.isInput(1)) {
      // do a membership test
      current_ = null;
      if (solutionsReturned_ == 0) {
        // we only do the membership test once
        solutionsReturned_++;
        Expr arg1 = evalMode_.getEnvir().lookup(element);
        if (set_.contains(arg1))
          result = true;
      }
    }
    else {
      // iterate through the members of set_
      if (solutionsReturned_ == 0) {
        // set up the iterator...
        current_ = set_.subsetIterator(element);
      }
      assert current_ != null;
      solutionsReturned_++;
      if (current_.hasNext()) {
        Expr value = (Expr)current_.next();
        evalMode_.getEnvir().setValue(element, value);
        result = true;
      }
    }
    return result;
  }

  /** Prints the FlatMember with optional bounds information. */
  @Override public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(super.toString());
    result.deleteCharAt(result.length()-1);  // delete the last ']'
    ZName setName = args_.get(0);
    EvalSet set = null;
    if (bounds_ != null && (set=bounds_.getEvalSet(setName)) != null) {
      result.append("::");
      BigInteger lo = set.getLower();
      if (lo != null)
        result.append(lo.toString());
      result.append("..");
      BigInteger hi = set.getUpper();
      if (hi != null)
        result.append(hi.toString());
    }
    result.append("]");
    return result.toString();
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatMemberVisitor)
      return ((FlatMemberVisitor<R>) visitor).visitFlatMember(this);
    else
      return super.accept(visitor);
  }
}
