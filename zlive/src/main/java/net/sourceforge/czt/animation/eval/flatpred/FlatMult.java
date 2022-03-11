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
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatMultVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/** FlatMult implements the a*b=c predicate.
 *  TODO: make it handle the IOI and OII cases more conservatively
 *     when one of those inputs might be zero.  (Use bounds information?)
 */
public class FlatMult extends FlatPred
{
  private Factory factory_ = new Factory();
  private Bounds bounds_ = null;
  
  public FlatMult(ZName a, ZName b, ZName c)
  {
    args_ = new ArrayList<ZName>(3);
    args_.add(a);
    args_.add(b);
    args_.add(c);
    solutionsReturned_ = -1;
  }

  @Override public boolean inferBounds(Bounds bnds)
  {
    bounds_ = bnds;
    // TODO: propagate bounds in all directions.
    //   Warning: this is very complex because of negatives and zero.
    return false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    assert bounds_ != null;
    ZName factor1 = args_.get(0);
    ZName factor2 = args_.get(1);
    Mode mode = modeOneOutput(env);
    // restrict the IOI mode to avoid zero.
    if (mode != null
        && mode.isInput(factor1) 
        && mode.isOutput(factor2)) {
      if (bounds_.includesZero(factor1)) {
        mode = null;
      }
      else {
        mode.setSolutions(Mode.MAYBE_ONE_SOLUTION); // eg. 3*y=5 will fail.
      }
    }
    // restrict the OII mode to avoid zero.
    if (mode != null
        && mode.isInput(factor2) 
        && mode.isOutput(factor1)) {
      if (bounds_.includesZero(factor2)) {
        mode = null;
      }
      else {
        mode.setSolutions(Mode.MAYBE_ONE_SOLUTION); // eg. x*3=5 will fail.
      }
    }
    return mode;
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
        throws EvalException
  {
    assert(evalMode_ != null);
    assert(solutionsReturned_ >= 0);
    boolean result = false;
    if(solutionsReturned_ == 0) {
      solutionsReturned_++;
      if (evalMode_.isInput(0) && evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        Expr c = evalMode_.getEnvir().lookup(args_.get(2));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = ((NumExpr)b).getValue();
        BigInteger z = ((NumExpr)c).getValue();
        if ((x.multiply(y)).equals(z))
          result = true;
      }
      else if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = ((NumExpr)b).getValue();
        BigInteger z = x.multiply(y);
        Expr c = factory_.createNumExpr(z);
        evalMode_.getEnvir().setValue(args_.get(2),c);
        result = true;
      }
      else if (evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        Expr c = evalMode_.getEnvir().lookup(args_.get(2));
        BigInteger y = ((NumExpr)b).getValue();
        if(y.equals(BigInteger.ZERO)) {
          throw new EvalException("Cannot solve multiplication by 0: " + (Name)args_.get(1));
        }
        else {
          BigInteger z = ((NumExpr)c).getValue();
          BigInteger x = z.divide(y);
          // we must check that this does indeed satisfy x*y=z.
          if (x.multiply(y).equals(z)) {
            Expr a = factory_.createNumExpr(x);
            evalMode_.getEnvir().setValue(args_.get(0),a);
            result = true;
          }
        }
      }
      else if (evalMode_.isInput(0) && evalMode_.isInput(2)) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        Expr c = evalMode_.getEnvir().lookup(args_.get(2));
        BigInteger x = ((NumExpr)a).getValue();
        if(x.equals(BigInteger.ZERO)) {
          throw new EvalException("Cannot solve multiplication by 0: " + args_.get(0));
        }
        else {
          BigInteger z = ((NumExpr)c).getValue();
          BigInteger y = z.divide(x);
          // we must check that this does indeed satisfy x*y=z.
          if (x.multiply(y).equals(z)) {
            Expr b = factory_.createNumExpr(y);
            evalMode_.getEnvir().setValue(args_.get(1),b);
            result = true;
          }
        }
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printBinOp("*");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatMultVisitor)
      return ((FlatMultVisitor<R>) visitor).visitFlatMult(this);
    else
      return super.accept(visitor);
  }
}
