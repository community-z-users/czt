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

import java.util.List;
import java.util.ArrayList;
import java.math.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatMult implements the a/b=c predicate. */
public class FlatDiv extends FlatPred
{
  private Factory factory_ = new Factory();

  public FlatDiv(RefName a, RefName b, RefName c)
  {
    args = new ArrayList(3);
    args.add(a);
    args.add(b);
    args.add(c);
    solutionsReturned = -1;
  }
//@ requires newargs.size() == 3;
  public FlatDiv(ArrayList newargs)
  {
    if (newargs == null || newargs.size() != 3)
      throw new IllegalArgumentException("FlatDiv requires 3 args");
    args = newargs;
    solutionsReturned = -1;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return modeFunction(env);
  }

  private BigInteger specialDivide(BigInteger a, BigInteger b)
  {
    if(a.compareTo(BigInteger.ZERO)<0) {
      if(b.compareTo(BigInteger.ZERO)<0)
        return (a.divide(b)).add(BigInteger.ONE);
      else
        return (a.divide(b)).subtract(BigInteger.ONE);
    }
    else 
      return a.divide(b);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  throws EvalException
  {
    assert(evalMode_ != null);
    assert(solutionsReturned >= 0);
    boolean result = false;
    if(solutionsReturned == 0) {
      solutionsReturned++;
      if (evalMode_.isInput(0) && evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr a = evalMode_.getEnvir().lookup((RefName)args.get(0));
        Expr b = evalMode_.getEnvir().lookup((RefName)args.get(1));
        Expr c = evalMode_.getEnvir().lookup((RefName)args.get(2));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = ((NumExpr)b).getValue();
        if(y.equals(BigInteger.ZERO)) {
          throw new EvalException("Cannot solve division by 0: " + (RefName)args.get(1));
        }
        else {
          BigInteger z = ((NumExpr)c).getValue();
          if ((specialDivide(x,y)).equals(z))
            result = true;
        }
      }
      else if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr a = evalMode_.getEnvir().lookup((RefName)args.get(0));
        Expr b = evalMode_.getEnvir().lookup((RefName)args.get(1));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = ((NumExpr)b).getValue();
        if(y.equals(BigInteger.ZERO)) {
          throw new EvalException("Cannot solve division by 0: " + (RefName)args.get(1));
        }
        else {
          BigInteger z = specialDivide(x,y);
          Expr c = factory_.createNumExpr(z);
          evalMode_.getEnvir().setValue((RefName)args.get(2),c);
          result = true;
        }
      }
    }
    return result;
  }
  
  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatDivVisitor) {
      FlatDivVisitor flatDivVisitor = (FlatDivVisitor) visitor;
      return flatDivVisitor.visitFlatDiv(this);
    }
    return super.accept(visitor);
  }
}
