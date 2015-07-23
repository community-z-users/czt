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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatProdVisitor;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.FuzzySet;
import net.sourceforge.czt.animation.eval.result.ProdSet;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
 * FlatProd([a,b,c...], s) implements a \cross b \cross c... = s.
 * It creates an EvalSet for s that hides the base sets
 * a,b,c... and can be used to do membership tests or to
 * enumerate all members (with no duplicates).
 *
 * @author marku
 */
public class FlatProd extends FlatPred
{
  /** The most recent bounds information. */
  protected Bounds bounds_;

  /** Creates a new instance of FlatUnion */
  public FlatProd(List<ZName> baseSets, ZName s)
  {
    assert baseSets.size() >= 2;
    args_ = new ArrayList<ZName>(baseSets);
    args_.add(s);
    solutionsReturned_ = -1;
  }

  /** This calculates the maximum and estimated size of the cartesian
   * product from the maximum and estimated sizes of the base sets.
   * TODO: could perform two-way bounds propagation similar to
   *   multiplication, but this is probably rarely useful.
   */
  public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    // calculate an upper bound on the size of the product
    BigInteger maxSize = BigInteger.ONE;
    double estSize = 1.0;
    for (int i=0; i<args_.size()-1; i++) {
      EvalSet set_i = bnds.getEvalSet(args_.get(i));
      if (set_i != null) {
        estSize *= set_i.estSize();
        BigInteger max_i = set_i.maxSize();
        if (max_i == null)
          maxSize = null;
        else if (maxSize != null)
          maxSize = maxSize.multiply(max_i);
      }
      else {
        maxSize = null;  // infinite now
        estSize *= EvalSet.UNKNOWN_SIZE;
      }
    }
    FuzzySet fuzzy = new FuzzySet(getLastArg().toString(), estSize, maxSize);
    return bnds.setEvalSet(getLastArg(), fuzzy);
  }

  /** TODO: could implement a reverse mode as well, but rarely useful. */
  public Mode chooseMode(Envir env)
  {
    assert bounds_ != null; // inferBounds should have been called.
    Mode m = modeFunction(env);
//    // April 2015 experiment: adding this does not make much difference to evaluate success.
//    if (m != null && m.isOutput(getLastArg())) {
//    	// Try to avoid generating cartesian products - they are usually large!
//      // But they can be used for testing membership, so we don't always have to generate all members.
//    	m.setSolutions(1.3);
//    }
    return m;
  }

  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    boolean result = false;
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      ZName set = getLastArg();
      Envir env = evalMode_.getEnvir();
      List<EvalSet> baseSets = findSets(env);
      if (baseSets == null)
        throw new EvalException("unevaluated base set in product "+this);
      EvalSet newSet = new ProdSet(baseSets);
      if (evalMode_.isInput(set)) {
        result = newSet.equals(env.lookup(set));
      }
      else {
        env.setValue(set, newSet);
        result = true;
      }
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

  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(printLastArg());
    result.append(" = ");
    for (int i=0; i<args_.size()-1; i++) {
      result.append(printArg(i));
      if (i < args_.size()-2)
        result.append(" x ");
    }
    return result.toString();
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
