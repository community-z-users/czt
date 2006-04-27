/**
 Copyright (C) 2005 Mark Utting
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
import java.math.BigInteger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.animation.eval.EvalSet;

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

  /** The left-hand EvalSet, once known. */
  private EvalSet leftSet_;

  /** The right-hand EvalSet, once known. */
  private EvalSet rightSet_;

  /** Used by nextMember to iterate through both sets. */
  private Iterator<Expr> memberIterator_ = null;

  /** Used by nextMember to know which set it is iterating through. 
   *  1 means leftSet_, 2 means rightSet_
   */
  private int membersFrom_ = 0;

  /** Creates a new instance of FlatUnion */
  public FlatUnion(ZRefName a, ZRefName b, ZRefName s)
  {
    args_ = new ArrayList<ZRefName>();
    args_.add(a);
    args_.add(b);
    args_.add(s);
    leftSet_ = null;
    rightSet_ = null;
    solutionsReturned_ = -1;
  }

  public Mode chooseMode(Envir env)
  {
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
      resetResult();
      boolean inputsKnown = findSets();
      assert inputsKnown;

      if (evalMode_.isInput(2)) {
        result = this.equals(evalMode_.getEnvir().lookup(args_.get(2)));
      }
      else {
        evalMode_.getEnvir().setValue(args_.get(2), this);
        result = true;
      }

      // now set up nextMember to start iterating through leftSet_
      memberIterator_ = leftSet_.iterator();
      membersFrom_ = 1;
    }
    return result;
  }

  /** Helper method to set leftSet_ and rightSet_, if possible.
   *  @return true iff both leftSet_ and rightSet_ are known.
   */
  //@ensures \result <==> leftSet_ != null && rightSet_ != null;
  protected boolean findSets()
  {
    if (leftSet_ == null || rightSet_ == null) {
      Envir env = getEnvir();
      if (env != null) {
        leftSet_ = (EvalSet) env.lookup(args_.get(0));
        rightSet_ = (EvalSet) env.lookup(args_.get(1));
      }
    }
    return leftSet_ != null && rightSet_ != null;
  }

  ///////////////////////////////////////////////////////////
  //  Methods inherited from EvalSet
  ///////////////////////////////////////////////////////////

  /** Numeric bounds information can flow both ways.
   *  Any bounds on s are propagated to a and b.
   *  Any bounds on a and b are combined via min/max and
   *  then propagated to s.
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    return bnds.setEvalSet(args_.get(args_.size() - 1), this);
  }

  /** The lower bound on numeric elements, if any, else null. */
  public BigInteger getLower()
  {
    BigInteger result = null;
    ZRefName a = args_.get(0);
    ZRefName b = args_.get(1);
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
    ZRefName a = args_.get(0);
    ZRefName b = args_.get(1);
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

  /** The maximum size of the set in the default environment.
   *  @return  Upper bound on the size of the set, or null if not known.
   . */
  public BigInteger maxSize()
  {
    if (findSets()) {
      BigInteger leftSize = leftSet_.maxSize();
      BigInteger rightSize = rightSet_.maxSize();
      if (leftSize != null && rightSize != null)
        return leftSize.add(rightSize);
    }
    return null;
  }

  /** Estimate the size of the set in the default environment.
   *  The default environment must have been set (via FlatPred.setMode)
   *  before you can call this.
   . */
  //@ requires getEnvir() != null;
  public double estSize()
  {
    if (findSets())
      return leftSet_.estSize() + rightSet_.estSize();
    else
      return EvalSet.UNKNOWN_SIZE;
  }

  /** Estimate the size of the set in a given environment. */
  public double estSize(Envir env)
  {
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
  public double estSubsetSize(Envir env, ZRefName elem)
  {
    EvalSet left = (EvalSet) env.lookup(args_.get(0));
    EvalSet right = (EvalSet) env.lookup((args_.get(1)));
    if (left != null && right != null)
      return left.estSubsetSize(env, elem) + right.estSubsetSize(env, elem);
    else
      return EvalSet.UNKNOWN_SIZE;
  }

  protected Expr nextMember()
  {
    assert solutionsReturned_ > 0; // nextEvaluation() must have succeeded.
    while (memberIterator_ != null) {
      if (memberIterator_.hasNext())
        return memberIterator_.next();
      else if (membersFrom_ == 1) {
        memberIterator_ = rightSet_.iterator();
        membersFrom_++;
      }
      else {
        memberIterator_ = null;
        membersFrom_++;
      }
    }
    return null;
  }

  /** Iterate through all members of this set that might
   *  equal element (which must be fully evaluated).
   *  The result will contain no duplicates.
   *  However, both subsets will be built before the
   *  iterator returns, so this might be expensive on space.
   *
   * @return an Iterator object.
   */
  public Iterator<Expr> subsetIterator(ZRefName element)
  {
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

  /** Tests for membership of the set.
   * @param e  The fully evaluated expression.
   * @return   true iff e is a member of the set.
   */
  //@ requires solutionsReturned > 0;
  public boolean contains(Object e)
  {
    return leftSet_.contains(e) || rightSet_.contains(e);
  }

  /**Tests for the equality of any two sets.
   Here, the equality is based upon both the sets
   having the same elements, not taking into consideration
   the duplication of elements.
   */
  public boolean equals(Object obj)
  {
    return equalsEvalSet(this, obj);
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
