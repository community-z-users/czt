/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import java.math.BigInteger;
import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatEqualsVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** FlatEquals implements the a = b predicate. */
public class FlatEquals extends FlatPred
{
  /** The most recent bounds object. */
  private Bounds bounds_;
  
  public FlatEquals(ZName a, ZName b)
  {
    args_ = new ArrayList<ZName>(2);
    args_.add(a);
    args_.add(b);
    solutionsReturned_ = -1;
  }

  /** Copies integer bounds from each arg to the other. */
  public boolean inferBounds(Bounds bnds)
  {
    boolean changed = false;
    ZName left = args_.get(0);
    ZName right = args_.get(1);

    // get all existing bounds, BEFORE we start adding bounds.
    BigInteger lmin = bnds.getLower(left);
    BigInteger lmax = bnds.getUpper(left);
    BigInteger rmin = bnds.getLower(right);
    BigInteger rmax = bnds.getUpper(right);

    // propagate bounds from left to right.
    if (lmin != null)
      changed |= bnds.addLower(right, lmin);
    if (lmax != null)
      changed |= bnds.addUpper(right, lmax);

    // propagate bounds from right to left.
    if (rmin != null)
      changed |= bnds.addLower(left, rmin);
    if (rmax != null)
      changed |= bnds.addUpper(left, rmax);

    // now record the actual equality
    bnds.addAlias(left, right);
    bounds_ = bnds;
    return changed;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
	// This is problematic for set equality, because it says cost=1.0
	// regardless of the possible expense/size of the set.
	// It would be nice to give preference to smaller sets.
    return modeOneOutput(env);
    /*
    // This is a draft attempt at finding information about the size of a set.
    // It is not very successful, because most of the sets in env have no information!
    // To make this work better, the inferBounds or choosemode methods of
    // FlatSetComp etc. need to record more useful information about the
    // size of the set (either in the environment, or in the Bounds object).
    // Then the following code should become more useful.
	Mode result = new Mode(this, env, getArgs(), 0.0);
	if (result.numOutputs() == 0)
		result.setSolutions(Mode.MAYBE_ONE_SOLUTION);
	else if (result.numOutputs() == 1) {
		// do we have a known input?
		Expr input = null;
		if (result.isInput(0)) {
			input = findSetInfo(args_.get(0), env);
		} else if (result.isInput(1)) {
			input = findSetInfo(args_.get(1), env);
		}
		// now try to estimate how complex the input value will be to evaluate
		if (input != null && input instanceof EvalSet) {
			EvalSet set = (EvalSet) input;
			double size = set.estSize();
			double logSize = Math.log10(size);
			System.out.println("Equals " + toString() + " EvalSet estSize=" + size + " logSize=" + logSize);
			result.setSolutions(logSize);
		} else if (input == null) {
			result.setSolutions(1.1); // 
			System.out.println("Equals " + toString() + " unknown so " + 1.1);
		} else {
			result.setSolutions(Mode.ONE_SOLUTION);
			System.out.println("Equals " + toString() + " 1.0");
		}
	}
	else {
		result = null;
	}
    return result;
    */
  }

  /** Tries to find approximate information about the given name. */
  protected Expr findSetInfo(ZName name, Envir env) {
	  Expr result = null;
	  if (env.isDefined(name)) {
		  result = env.lookup(name);
		  if (result != null) {
			  System.out.println("FOUND env info for " + name + " : " + result);
			  return result;
		  }
	  }
	  // try a synonym of name?
	  ZName bestName = bounds_.getBestAlias(name);
	  if (env.isDefined(bestName)) {
		  result = env.lookup(bestName);
	  }
	  if (result != null) {
		  System.out.println("FOUND env info for " + name + " : " + result);
		  return result;
	  }
	  // try getting approx info from bounds.
	  result = bounds_.getEvalSet(bestName); // approximate
	  if (result != null) {
		  System.out.println("FOUND bounds eval set info for " + name + " : " + result);
	  }
	  return result;
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert(evalMode_ != null);
    assert(solutionsReturned_ >= 0);
    boolean result = false;
    if(solutionsReturned_==0)
    {
      solutionsReturned_++;
      if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        ExprComparator comp = ExprComparator.create();
        if(comp.compare(a,b) == 0)
          result = true;
      }
      else if (evalMode_.isInput(0)) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        evalMode_.getEnvir().setValue(args_.get(1),a);
        result = true;
      }
      else if (evalMode_.isInput(1)) {
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        evalMode_.getEnvir().setValue(args_.get(0),b);
        result = true;
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printArg(0) + " = " + printArg(1);
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatEqualsVisitor)
      return ((FlatEqualsVisitor<R>) visitor).visitFlatEquals(this);
    else
      return super.accept(visitor);
  }
}
