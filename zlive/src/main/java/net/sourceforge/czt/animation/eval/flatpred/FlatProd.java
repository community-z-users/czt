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
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.animation.eval.EvalSet;

/**
 * FlatProd([a,b,c...], s) implements a \cross b \cross c... = s.
 * It creates an EvalSet for s that hides the base sets
 * a,b,c... and can be used to do membership tests or to
 * enumerate all members (with no duplicates).
 *
 * @author marku
 */
public class FlatProd extends FlatEvalSet
{
  /** The most recent bounds information. */
  protected Bounds bounds_;

  /** The actual values of the base sets, once known. */
  private List<EvalSet> baseSets_;

  /** Used by nextMember to iterate through both sets. */
  private List<Iterator<Expr>> iterators_ = null;

  /** Creates a new instance of FlatUnion */
  public FlatProd(List<ZRefName> baseSets, ZRefName s)
  {
    args_ = new ArrayList<ZRefName>(baseSets);
    args_.add(s);
    solutionsReturned_ = -1;
  }

  /** TODO: implement the reverse mode as well. */
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
      resetResult();
      ZRefName set = getLastArg();
      Envir env = evalMode_.getEnvir();
      baseSets_ = findSets(env);
      if (baseSets_ == null)
        throw new EvalException("unevaluated base set in product "+this);

      if (evalMode_.isInput(set)) {
        result = this.equals(env.lookup(set));
      }
      else {
        env.setValue(set, this);
        result = true;
      }

      // reset iterators
      iterators_ = null;
    }
    return result;
  }

  /** Helper method to search for all the base sets.
   *  @return null if some are not known yet.
   */
  protected List<EvalSet> findSets(Envir env)
  {
      List<EvalSet> sets = new ArrayList<EvalSet>();
      for (int i=0; i<args_.size()-1; i++) {
        Expr set_i = env.lookup(args_.get(i));
        if (set_i instanceof EvalSet)
          sets.add( (EvalSet)set_i);
        else
          return null;
      }
      return sets;
  }

  ///////////////////////////////////////////////////////////
  //  Methods inherited from EvalSet
  ///////////////////////////////////////////////////////////

  /** TODO: perform bounds propagation similar to multiplication.
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    return bnds.setEvalSet(getLastArg(), this);
  }

  /** TODO: implement more accurate maxSize().
   */
  @Override public BigInteger maxSize()
  {
    return super.maxSize();
  }

  /** TODO: implement more accurate estSize(...).
   */
  public double estSize(Envir env)
  {
    return Double.MAX_VALUE;
  }

  /** TODO: implement nextMember properly */
  protected Expr nextMember()
  {
    throw new EvalException("FlatProd does not implement nextMember yet.");
    /*
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
    */
  }

  //@ requires solutionsReturned > 0;
  public boolean contains(Object e)
  {
    assert bounds_ != null; // inferBounds should have been called.
    if ( ! (e instanceof TupleExpr))
      throw new EvalException("unevaluated tuple: "+e);

    TupleExpr tuple = (TupleExpr) e;
    List<Expr> values = tuple.getZExprList();
    if (values.size() != baseSets_.size())
      throw new EvalException("type error in FlatProd: "+e);
    for (int i=0; i<values.size(); i++) {
      if ( ! baseSets_.get(i).contains(values.get(i)))
        return false;
    }
    return true;
  }


  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatProdVisitor)
      return ((FlatProdVisitor<R>) visitor).visitFlatProd(this);
    else
      return super.accept(visitor);
  }
}
