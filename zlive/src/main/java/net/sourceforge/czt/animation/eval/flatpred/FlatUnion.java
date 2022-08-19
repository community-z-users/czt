/**
 Copyright (C) 2006 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.*;
import java.math.BigInteger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatUnionVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.animation.eval.result.UnionSet;

/**
 * FlatUnion(a, b, r) implements a \cup b = s.
 * It creates an EvalSet for s, that hides the two subsets
 * a and b and can be used to do membership tests or to
 * enumerate all members (with duplicates removed).
 *
 * @author leo and marku
 */
public class FlatUnion extends FlatEvalSet
{
  /** The most recent variable bounds information. */
  protected Bounds bounds_;

  /** Creates a new instance of FlatUnion */
  public FlatUnion(ZName a, ZName b, ZName s)
  {
    args_ = new ArrayList<ZName>();
    args_.add(a);
    args_.add(b);
    args_.add(s);
    solutionsReturned_ = -1;
  }

  /** Numeric bounds information can flow both ways.
   *  Any bounds on s are propagated to a and b.
   *  Any bounds on a and b are combined via min/max and
   *  then propagated to s.
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    // bind getLastArg() to a fuzzyset to record approx sizes.
    EvalSet left = bnds.getEvalSet(args_.get(0));
    EvalSet right = bnds.getEvalSet(args_.get(1));
    double estSize = EvalSet.UNKNOWN_SIZE;
    BigInteger maxSize = null;
    if (left != null && right != null) {
      estSize = left.estSize() + right.estSize();
      BigInteger leftMax = left.maxSize();
      BigInteger rightMax = left.maxSize();
      if (leftMax != null && rightMax != null)
        maxSize = leftMax.add(rightMax);
    }
    FuzzySet fuzzy = new FuzzySet(getLastArg().toString(), estSize, maxSize);
    return bnds.setEvalSet(args_.get(args_.size() - 1), fuzzy);
  }

  public Mode chooseMode(Envir env)
  {
    assert bounds_ != null; // inferBounds should have been called.
    Mode m = modeFunction(env);
    return m;
  }

  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    boolean result = false;
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      Envir env = evalMode_.getEnvir();
      Expr left = env.lookup(args_.get(0));
      Expr right = env.lookup(args_.get(1));
      assert left instanceof EvalSet;
      assert right instanceof EvalSet;
      UnionSet set = new UnionSet((EvalSet)left, (EvalSet)right);
      if (evalMode_.isInput(2)) {
        result = set.equals(env.lookup(args_.get(2)));
      }
      else {
        evalMode_.getEnvir().setValue(args_.get(2), set);
        result = true;
      }
    }
    return result;
  }

  ///////////////////////////////////////////////////////////
  //  Methods inherited from EvalSet
  ///////////////////////////////////////////////////////////

  /** The lower bound on numeric elements, if any, else null. */
  // TODO: incorporate these into inferBounds???
  public BigInteger getLower()
  {
    BigInteger result = null;
    ZName a = args_.get(0);
    ZName b = args_.get(1);
    EvalSet left = (EvalSet) bounds_.getEvalSet(a);
    EvalSet right = (EvalSet) bounds_.getEvalSet(b);
    if (left != null && right != null) {
      BigInteger leftLower = left.getLower();
      BigInteger rightLower = right.getLower();
      if (leftLower != null && rightLower != null)
        result = leftLower.min(rightLower);
    }
    return result;
  }

  /** The upper bound on numeric elements, if any, else null. */
  public BigInteger getUpper()
  {
    BigInteger result = null;
    ZName a = args_.get(0);
    ZName b = args_.get(1);
    EvalSet left = (EvalSet) bounds_.getEvalSet(a);
    EvalSet right = (EvalSet) bounds_.getEvalSet(b);
    if (left != null && right != null) {
      BigInteger leftUpper = left.getUpper();
      BigInteger rightUpper = right.getUpper();
      if (leftUpper != null && rightUpper != null)
        result = leftUpper.max(rightUpper);
    }
    return result;
  }


  /** Estimate the size of the set in a given environment. */
  // TODO: remove this???
  public double estSize(Envir env)
  {
    assert bounds_ != null; // inferBounds should have been called.
    EvalSet left = (EvalSet) env.lookup(args_.get(0));
    EvalSet right = (EvalSet) env.lookup((args_.get(1)));
    if (left != null && right != null) {
      return left.estSize() + right.estSize();
    }
    else
      return EvalSet.UNKNOWN_SIZE;
  }

  /** Estimate the size of {x:this | x=elem} in a given environment.
   *  This allows the bounds of elem to be used to reduce the size of set.
   */
  // TODO: remove this???
  public double estSubsetSize(Envir env, ZName elem)
  {
    assert bounds_ != null; // inferBounds should have been called.
    EvalSet left = (EvalSet) env.lookup(args_.get(0));
    EvalSet right = (EvalSet) env.lookup((args_.get(1)));
    if (left != null && right != null)
      return left.estSubsetSize(env, elem) + right.estSubsetSize(env, elem);
    else
      return EvalSet.UNKNOWN_SIZE;
  }

  /** Iterate through all members of this set that might
   *  equal element (which must be fully evaluated).
   *  The result will contain no duplicates.
   *  However, both subsets will be built before the
   *  iterator returns, so this might be expensive on space.
   *
   * @return an Iterator object.
   *  TODO: delete this???
  public Iterator<Expr> subsetIterator(ZName element)
  {
    assert bounds_ != null; // inferBounds should have been called.
    assert solutionsReturned_ > 0; // nextEvaluation() must have succeeded.
    Set<Expr> subset = new HashSet<Expr>();
    // generate all subset members from BOTH sets.
    // Any duplicates will be removed, thanks to the HashSet.
    Iterator<Expr> elems = leftSet_.subsetIterator(element);
    while (elems.hasNext())
      subset.add(elems.next());
    elems = rightSet_.subsetIterator(element);
    while (elems.hasNext())
      subset.add(elems.next());
    return subset.iterator();
  }
*/

  @Override
  public String toString()
  {
    return printBinOp("u");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatUnionVisitor)
      return ((FlatUnionVisitor<R>) visitor).visitFlatUnion(this);
    else
      return super.accept(visitor);
  }
}
