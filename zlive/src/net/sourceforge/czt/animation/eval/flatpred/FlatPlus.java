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
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatPlus implements the a+b=c predicate. */
public class FlatPlus extends FlatPred
{
  private Factory factory_ = new Factory();

  public FlatPlus(ZRefName a, ZRefName b, ZRefName c)
  {
    args = new ArrayList<ZRefName>(3);
    args.add(a);
    args.add(b);
    args.add(c);
    solutionsReturned = -1;
  }
  
  //@ requires newargs.size() == 3;
  public FlatPlus(ArrayList newargs)
  {
    if (newargs == null || newargs.size() != 3)
      throw new IllegalArgumentException("FlatPlus requires 3 args");
    args = newargs;
    solutionsReturned = -1;
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
    assert(solutionsReturned >= 0);
    boolean result = false;
    if (solutionsReturned == 0) {
      solutionsReturned++;
      if (evalMode_.isInput(0) && evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr arg0 = evalMode_.getEnvir().lookup(args.get(0));
        Expr arg1 = evalMode_.getEnvir().lookup(args.get(1));
        Expr arg2 = evalMode_.getEnvir().lookup(args.get(2));
        BigInteger arg0Value = ((NumExpr)arg0).getValue();
        BigInteger arg1Value = ((NumExpr)arg1).getValue();
        BigInteger arg2Value = ((NumExpr)arg2).getValue();
        if((arg0Value.add(arg1Value)).equals(arg2Value))
          result = true;
      }
      else if (evalMode_.isInput(1) && evalMode_.isInput(2)) {
        Expr arg1 = evalMode_.getEnvir().lookup(args.get(1));
        Expr arg2 = evalMode_.getEnvir().lookup(args.get(2));
        BigInteger arg1Value = ((NumExpr)arg1).getValue();
        BigInteger arg2Value = ((NumExpr)arg2).getValue();
        BigInteger arg0Value = arg2Value.subtract(arg1Value);
        Expr arg0 = factory_.createNumExpr(arg0Value);
        evalMode_.getEnvir().setValue(args.get(0),arg0);
        result = true;
      }
       else if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr arg0 = evalMode_.getEnvir().lookup(args.get(0));
        Expr arg1 = evalMode_.getEnvir().lookup(args.get(1));
        BigInteger arg0Value = ((NumExpr)arg0).getValue();
        BigInteger arg1Value = ((NumExpr)arg1).getValue();
        BigInteger arg2Value = arg0Value.add(arg1Value);
        Expr arg2 = factory_.createNumExpr(arg2Value);
        evalMode_.getEnvir().setValue(args.get(2),arg2);
        result = true;
      }
     else if (evalMode_.isInput(0) && evalMode_.isInput(2)) {
        Expr arg0 = evalMode_.getEnvir().lookup(args.get(0));
        Expr arg2 = evalMode_.getEnvir().lookup(args.get(2));
        BigInteger arg0Value = ((NumExpr)arg0).getValue();
        BigInteger arg2Value = ((NumExpr)arg2).getValue();
        BigInteger arg1Value = arg2Value.subtract(arg0Value);
        Expr arg1 = factory_.createNumExpr(arg1Value);
        evalMode_.getEnvir().setValue(args.get(1),arg1);
        result = true;
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatPlusVisitor) {
      FlatPlusVisitor flatPlusVisitor = (FlatPlusVisitor) visitor;
      return flatPlusVisitor.visitFlatPlus(this);
    }
    return super.accept(visitor);
  }
}
