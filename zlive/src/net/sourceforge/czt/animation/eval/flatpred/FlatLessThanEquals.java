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
import java.math.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatPlus implements the a <= b predicate. */
public class FlatLessThanEquals extends FlatPred
{
  protected RefName args[] = new RefName[2];
  protected BigInteger next;
  protected boolean evalFlag_;

  public FlatLessThanEquals(RefName a, RefName b)
  {
    args[0] = a;
    args[1] = b;
    next = null;
    evalFlag_ = false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    BigInteger zero = new BigInteger("0");
    Expr zilch = factory_.createNumExpr(zero);
    Mode m = null;
    boolean[] inputs = new boolean[2];
    double solutions;
    if( (env.isDefined(args[0])) && (env.isDefined(args[1])) ) {
      inputs[0] = true;
      inputs[1] = true;
      solutions = 0.5;
      m = new Mode(env,inputs,solutions);
    }
    else if ((env.isDefined(args[0]))) {
      inputs[0] = true;
      inputs[1] = false;
      solutions = Double.MAX_VALUE;
      env = env.add(args[1],null);
      m = new Mode(env,inputs,solutions);
    }
    else if ((env.isDefined(args[1]))) {
      inputs[0] = false;
      inputs[1] = true;
      solutions = Double.MAX_VALUE;
      env = env.add(args[0],null);
      m = new Mode(env,inputs,solutions);
    }
    return m;
  }

  /** Sets the flag for evaluation to true */
  public void startEvaluation()
  { evalFlag_ = true;
    next = null;
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    BigInteger one = new BigInteger("1");
    boolean result = false;
    if(evalFlag_)
    {
      if (evalMode_!=null) {
        if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
          evalFlag_ = false;
          Expr a = evalMode_.getEnvir().lookup(args[0]);
          Expr b = evalMode_.getEnvir().lookup(args[1]);
          BigInteger x = ((NumExpr)a).getValue();
          BigInteger y = ((NumExpr)b).getValue();
          if(x.compareTo(y)<=0)
            result = true;
          }
        else if (evalMode_.isInput(0)) {
          if (next == null) {
            Expr a = evalMode_.getEnvir().lookup(args[0]);
            BigInteger x = ((NumExpr)a).getValue();
            next = x;
          }
          else
            next = next.add(one);
          BigInteger y = next;
          Expr b = factory_.createNumExpr(y);
          evalMode_.getEnvir().setValue(args[1],b);
          result = true;
        }
        else if (evalMode_.isInput(1)) {
          if (next == null) {
            Expr b = evalMode_.getEnvir().lookup(args[1]);
            BigInteger y = ((NumExpr)b).getValue();
            next = y;
          }
          else
            next = next.subtract(one);
          BigInteger x = next;
          Expr a = factory_.createNumExpr(x);
          evalMode_.getEnvir().setValue(args[0],a);
          result = true;
        }
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatLessThanEqualsVisitor) {
      FlatLessThanEqualsVisitor v = (FlatLessThanEqualsVisitor) visitor;
      return v.visitFlatLessThanEquals(this);
    }
    return super.accept(visitor);
  }

  public /*@non_null@*/ Object[] getChildren()
  {
    return args;
  }

  public /*@non_null@*/ Term create(Object[] args)
  {
    try {
      RefName a = (RefName) args[0];
      RefName b = (RefName) args[1];
      return new FlatLessThanEquals(a, b);
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
  }
}
