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

/** FlatPlus implements the a+b=c predicate. */
public class FlatPlus extends FlatPred
			      // implements MemPred
{
  protected RefName args[] = new RefName[3];
  protected boolean evalFlag_;

  public FlatPlus(RefName a, RefName b, RefName c)
  {
    args[0] = a;
    args[1] = b;
    args[2] = c;
    evalFlag_ = false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    BigInteger zero = new BigInteger("0");
    Expr zilch = factory_.createNumExpr(zero);
    Mode m = null;
    boolean[] inputs = new boolean[3];
    double solutions;
    if( (env.lookup(args[0])!=null) && (env.lookup(args[1])!=null) && (env.lookup(args[2])!=null)) {
      inputs[0] = true;
      inputs[1] = true;
      inputs[2] = true;
      solutions = 0.5;
      m = new Mode(env,inputs,solutions);
    }
    else if ((env.lookup(args[0])!=null) && (env.lookup(args[1])!=null)) {
      inputs[0] = true;
      inputs[1] = true;
      inputs[2] = false;
      solutions = 1.0;
      env = env.add(args[2],zilch);
      m = new Mode(env,inputs,solutions);
    }
    else if ((env.lookup(args[0])!=null) && (env.lookup(args[2])!=null)) {
      inputs[0] = true;
      inputs[1] = false;
      inputs[2] = true;
      solutions = 1.0;
      env = env.add(args[1],zilch);
      m = new Mode(env,inputs,solutions);
    }
    else if ((env.lookup(args[1])!=null) && (env.lookup(args[2])!=null)) {
      inputs[0] = false;
      inputs[1] = true;
      inputs[2] = true;
      solutions = 1.0;
      env = env.add(args[0],zilch);
      m = new Mode(env,inputs,solutions);
    }
    return m;
  }

  /** Sets the flag for evaluation to true */
  public void startEvaluation()
  { evalFlag_ = true; }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    boolean result = false;
    if(evalFlag_)
    {
      if (evalMode_!=null) {
        if (evalMode_.isInput(0) && evalMode_.isInput(1) && evalMode_.isInput(2)) {
          evalFlag_ = false;
          Expr a = evalMode_.getEnvir().lookup(args[0]);
          Expr b = evalMode_.getEnvir().lookup(args[1]);
          Expr c = evalMode_.getEnvir().lookup(args[2]);
          BigInteger x = ((NumExpr)a).getValue();
          BigInteger y = ((NumExpr)b).getValue();
          BigInteger z = ((NumExpr)c).getValue();
          if((x.add(y)).equals(z))
            result = true;
          }
        else if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
          evalFlag_ = false;
          Expr a = evalMode_.getEnvir().lookup(args[0]);
          Expr b = evalMode_.getEnvir().lookup(args[1]);
          BigInteger x = ((NumExpr)a).getValue();
          BigInteger y = ((NumExpr)b).getValue();
          BigInteger z = x.add(y);
          Expr c = factory_.createNumExpr(z);
          evalMode_.getEnvir().setValue(args[2],c);
          result = true;
        }
        else if (evalMode_.isInput(1) && evalMode_.isInput(2)) {
          evalFlag_ = false;
          Expr b = evalMode_.getEnvir().lookup(args[1]);
          Expr c = evalMode_.getEnvir().lookup(args[2]);
          BigInteger y = ((NumExpr)b).getValue();
          BigInteger z = ((NumExpr)c).getValue();
          BigInteger x = z.subtract(y);
          Expr a = factory_.createNumExpr(x);
          evalMode_.getEnvir().setValue(args[0],a);
          result = true;
        }
        else if (evalMode_.isInput(0) && evalMode_.isInput(2)) {
          evalFlag_ = false;
          Expr a = evalMode_.getEnvir().lookup(args[0]);
          Expr c = evalMode_.getEnvir().lookup(args[2]);
          BigInteger x = ((NumExpr)a).getValue();
          BigInteger z = ((NumExpr)c).getValue();
          BigInteger y = z.subtract(x);
          Expr b = factory_.createNumExpr(y);
          evalMode_.getEnvir().setValue(args[1],b);
          result = true;
        }
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  /** @czt.todo Implement this properly. */
  public Object accept(Visitor visitor)
  { //TODO: call memPredVisitor
    return super.accept(visitor);
  }

  /** @czt.todo Implement this properly. */
  public /*@non_null@*/ Object[] getChildren()
  { return new Object[0]; }

  /** @czt.todo Implement this properly. */
  public Term /*@non_null@*/ create(Object[] args)
  { throw new RuntimeException("create not implemented"); }
}
