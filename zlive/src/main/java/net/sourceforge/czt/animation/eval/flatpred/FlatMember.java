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
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatMemberVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
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

  /** Returns the set of arguments that already have known values.
   *  (though the values may be null at chooseMode time).
   * @param env  The environment in which to look for the values
   * @return     null if no args are known.
   */
  protected Map<Object, Expr> knownValues(Envir env)
  {
    Map<Object, ZName> argNames = bounds_.getStructure(args_.get(1));
    Map<Object, Expr> argValues = null;
    if (argNames != null) {
      for (Map.Entry<Object, ZName> e : argNames.entrySet()) {
        if (env.isDefined(e.getValue())) {
          if (argValues == null)
            argValues = new HashMap<Object,Expr>();
          argValues.put(e.getKey(), env.lookup(e.getValue()));
        }
      }
    }
    return argValues;
  }

  public Mode chooseMode(Envir env)
  {
    assert bounds_ != null;
    // the set must be defined in env.
    ZName setName = args_.get(0);
    ZName elemName = args_.get(1);
    Mode result = new Mode(this, env, args_, Mode.MAYBE_ONE_SOLUTION);
    // is the set an input?
    if (result.isInput(setName)) {
      if (result.isOutput(elemName)) {
        // We will have to generate all members, so recalculate # of solns.
        // The actual EvalSet object will be available at evaluation
        // time, but we check to see if it is already available.
        // If it is, we can get better estimates.
        result.setSolutions(Double.POSITIVE_INFINITY); // worst case
        Expr e = env.lookup(setName);
        if (e == null)
          e = bounds_.getEvalSet(setName);
        if (e != null && e instanceof EvalSet) {
          EvalSet set = (EvalSet) e;
          RangeSet range = bounds_.getRange(elemName);
          if (range == null)
            range = new RangeSet(set.getLower(), set.getUpper());
          else
            range = range.intersect(set.getLower(), set.getUpper());
          BigInteger size = range.maxSize();
          // the size of the set is another limit on the number of solutions
          size = RangeSet.minPos(size, set.maxSize());
          // now translate size to double and use min(size,set.estSize())
          double solns = 100.0; //set.estSize();   TODO better estimate
          if (size != null)
            solns = Math.min(solns, size.doubleValue());
          result.setSolutions(solns);
        }
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
    assert bounds_ != null;
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
      // iterate through (some of) the members of set_
      if (solutionsReturned_ == 0) {
        // set up an iterator...
        Map<Object, Expr> argValues = knownValues(evalMode_.getEnvir0());
        if (argValues != null)
          current_ = set_.matchIterator(argValues);
        else
          current_ = set_.subsetIterator(bounds_.getRange(element));
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
    result.append(printArg(1));
    if (evalMode_ != null) {
      Map<Object, Expr> known = knownValues(evalMode_.getEnvir0());
      if (known != null) {
        result.append(known.toString());
      }
    }
    result.append(" in ");
    result.append(printArg(0));
    ZName setName = args_.get(0);
    EvalSet set = null;
    RangeSet range = null;
    if (bounds_ != null) {
      set = bounds_.getEvalSet(setName);
      range = bounds_.getRange(getLastArg());
    }
    if (set != null || range != null) {
      result.append(" :: ");
      if (set != null) {
        if (set.estSize() < Double.POSITIVE_INFINITY) {
          result.append(set.estSize());
          result.append(" ");
        }
        // now calculate range intersection of setName and set.
        BigInteger lo = set.getLower();
        BigInteger hi = set.getUpper();
        RangeSet elemRange = null;
        if (lo != null || hi != null)
          elemRange = new RangeSet(lo,hi);
        if (range == null)
          range = elemRange;
        else
          range = range.intersect(elemRange);
      }
      if (range != null) {
        result.append(range.toString());
      }
    }
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
