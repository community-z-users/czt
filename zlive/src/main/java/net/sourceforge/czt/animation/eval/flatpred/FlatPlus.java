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
import net.sourceforge.czt.animation.eval.flatvisitor.FlatPlusVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/** FlatPlus implements the a+b=c predicate. */
public class FlatPlus extends FlatPred
{
  private Factory factory_ = new Factory();

  public FlatPlus(ZName a, ZName b, ZName c)
  {
    args_ = new ArrayList<ZName>(3);
    args_.add(a);
    args_.add(b);
    args_.add(c);
    solutionsReturned_ = -1;
  }

  public boolean inferBounds(Bounds bnds)
  {
    boolean changed = false;
    ZName a = args_.get(0);
    ZName b = args_.get(1);
    ZName c = args_.get(2);

    BigInteger amin = bnds.getLower(a);
    BigInteger amax = bnds.getUpper(a);
    BigInteger bmin = bnds.getLower(b);
    BigInteger bmax = bnds.getUpper(b);
    BigInteger cmin = bnds.getLower(c);
    BigInteger cmax = bnds.getUpper(c);

    // propagate bounds to c.
    if (amin != null && bmin != null)
      changed |= bnds.addLower(c, amin.add(bmin));
    if (amax != null && bmax != null)
      changed |= bnds.addUpper(c, amax.add(bmax));

    // propagate bounds to a.
    if (cmin != null && bmax != null)
      changed |= bnds.addLower(a, cmin.add(bmax.negate()));
    if (cmax != null && bmin != null)
      changed |= bnds.addUpper(a, cmax.add(bmin.negate()));

    // propagate bounds to b.
    if (cmin != null && amax != null)
      changed |= bnds.addLower(b, cmin.add(amax.negate()));
    if (cmax != null && amin != null)
      changed |= bnds.addUpper(b, cmax.add(amin.negate()));

    return changed;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return modeOneOutput(env);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert(evalMode_ != null);
    assert(solutionsReturned_ >= 0);
    boolean result = false;
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      if (evalMode_.isInput(0) && evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr arg0 = evalMode_.getEnvir().lookup(args_.get(0));
        Expr arg1 = evalMode_.getEnvir().lookup(args_.get(1));
        Expr arg2 = evalMode_.getEnvir().lookup(args_.get(2));
        BigInteger arg0Value = ((NumExpr)arg0).getValue();
        BigInteger arg1Value = ((NumExpr)arg1).getValue();
        BigInteger arg2Value = ((NumExpr)arg2).getValue();
        if((arg0Value.add(arg1Value)).equals(arg2Value))
          result = true;
      }
      else if (evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr arg1 = evalMode_.getEnvir().lookup(args_.get(1));
        Expr arg2 = evalMode_.getEnvir().lookup(args_.get(2));
        BigInteger arg1Value = ((NumExpr)arg1).getValue();
        BigInteger arg2Value = ((NumExpr)arg2).getValue();
        BigInteger arg0Value = arg2Value.subtract(arg1Value);
        Expr arg0 = factory_.createNumExpr(arg0Value);
        evalMode_.getEnvir().setValue(args_.get(0),arg0);
        result = true;
      }
       else if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr arg0 = evalMode_.getEnvir().lookup(args_.get(0));
        Expr arg1 = evalMode_.getEnvir().lookup(args_.get(1));
        BigInteger arg0Value = ((NumExpr)arg0).getValue();
        BigInteger arg1Value = ((NumExpr)arg1).getValue();
        BigInteger arg2Value = arg0Value.add(arg1Value);
        Expr arg2 = factory_.createNumExpr(arg2Value);
        evalMode_.getEnvir().setValue(args_.get(2),arg2);
        result = true;
      }
     else if (evalMode_.isInput(0) && evalMode_.isInput(2)) {
        Expr arg0 = evalMode_.getEnvir().lookup(args_.get(0));
        Expr arg2 = evalMode_.getEnvir().lookup(args_.get(2));
        BigInteger arg0Value = ((NumExpr)arg0).getValue();
        BigInteger arg2Value = ((NumExpr)arg2).getValue();
        BigInteger arg1Value = arg2Value.subtract(arg0Value);
        Expr arg1 = factory_.createNumExpr(arg1Value);
        evalMode_.getEnvir().setValue(args_.get(1),arg1);
        result = true;
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printBinOp("+");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatPlusVisitor)
      return ((FlatPlusVisitor<R>) visitor).visitFlatPlus(this);
    else
      return super.accept(visitor);
  }
}
