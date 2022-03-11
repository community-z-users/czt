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
import net.sourceforge.czt.animation.eval.flatvisitor.FlatLessThanEqualsVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/** FlatPlus implements the a <= b predicate. */
public class FlatLessThanEquals extends FlatPred
{
  protected BigInteger next;
  private Factory factory_ = new Factory();

  public FlatLessThanEquals(ZName a, ZName b)
  {
    args_ = new ArrayList<ZName>(2);
    args_.add(a);
    args_.add(b);
    solutionsReturned_ = -1;
  }

  public boolean inferBounds(Bounds bnds)
  {
    boolean changed = false;
    ZName left = args_.get(0);
    ZName right = args_.get(1);

    // propagate upper bound from right to left.
    BigInteger rmax = bnds.getUpper(right);
    if (rmax != null)
      changed |= bnds.addUpper(left, rmax);

    // propagate lower bound from left to right.
    BigInteger lmin = bnds.getLower(left);
    if (lmin != null)
      changed |= bnds.addLower(right, lmin);

    return changed;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeOneOutput(env);
    if(m!=null) 
      if(m.numOutputs() > 0)
        m.setSolutions(Double.MAX_VALUE);
    return m;
  }
  
  public void startEvaluation() 
  {
    solutionsReturned_ = 0;
    next = null;
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation() {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    boolean result = false;
    solutionsReturned_++;
    if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
      if (solutionsReturned_ == 1) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        BigInteger x = ((NumExpr) a).getValue();
        BigInteger y = ((NumExpr) b).getValue();
        if (x.compareTo(y) <= 0)
          result = true;
      }
    }
    else if (evalMode_.isInput(0)) {
      if (next == null) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        BigInteger x = ((NumExpr) a).getValue();
        next = x;
      }
      else
        next = next.add(BigInteger.ONE);
      BigInteger y = next;
      Expr b = factory_.createNumExpr(y);
      evalMode_.getEnvir().setValue(args_.get(1), b);
      result = true;
    }
    else if (evalMode_.isInput(1)) {
      if (next == null) {
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        BigInteger y = ((NumExpr) b).getValue();
        next = y;
      }
      else
        next = next.subtract(BigInteger.ONE);
      BigInteger x = next;
      Expr a = factory_.createNumExpr(x);
      evalMode_.getEnvir().setValue(args_.get(0), a);
      result = true;
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printArg(0) + " <= " + printArg(1);
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatLessThanEqualsVisitor)
      return ((FlatLessThanEqualsVisitor<R>) visitor).visitFlatLessThanEquals(this);
    else
      return super.accept(visitor);
  }
}
