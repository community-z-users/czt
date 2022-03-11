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
import net.sourceforge.czt.animation.eval.UndefException;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatModVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/** FlatMult implements the a/b=c predicate. */
public class FlatMod extends FlatPred
{
  private Factory factory_ = new Factory();

  public FlatMod(ZName a, ZName b, ZName c)
  {
    args_ = new ArrayList<ZName>(3);
    args_.add(a);
    args_.add(b);
    args_.add(c);
    solutionsReturned_ = -1;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return modeFunction(env);
  }

  private BigInteger specialDivide(BigInteger a, BigInteger b)
  {
    BigInteger answer = a.divide(b);
    if (((a.compareTo(BigInteger.ZERO)<0)&&(b.compareTo(BigInteger.ZERO)>0)) ||
        ((a.compareTo(BigInteger.ZERO)>0)&&(b.compareTo(BigInteger.ZERO)<0))) {
      if (!(answer.multiply(b).equals(a)))
        answer = answer.subtract(BigInteger.ONE);
    }
    return answer;
  }

  private BigInteger specialMod(BigInteger a, BigInteger b)
  {
    return a.subtract((specialDivide(a,b)).multiply(b));
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
        if(y.equals(BigInteger.ZERO)) {
	  throw new UndefException(args_.get(0) + " mod 0");
        }
        else {
          BigInteger z = ((NumExpr)c).getValue();
          if ((specialMod(x,y)).equals(z))
            result = true;
        }
      }
      else if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        Expr b = evalMode_.getEnvir().lookup(args_.get(1));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = ((NumExpr)b).getValue();
        if(y.equals(BigInteger.ZERO)) {
	  throw new UndefException(args_.get(0) + " mod 0");
        }
        else {
          BigInteger z = specialMod(x,y);
          Expr c = factory_.createNumExpr(z);
          evalMode_.getEnvir().setValue(args_.get(2),c);
          result = true;
        }
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return printBinOp("mod");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatModVisitor)
      return ((FlatModVisitor<R>) visitor).visitFlatMod(this);
    else
      return super.accept(visitor);
  }
}
