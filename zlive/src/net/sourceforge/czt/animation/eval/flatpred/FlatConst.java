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

/** FlatPlus implements the var = const predicate. */
public class FlatConst extends FlatPred
{
  protected RefName args[] = new RefName[1];
  protected Expr constant;
  protected boolean evalFlag_;

  public FlatConst(RefName a, Expr b)
  {
    args[0] = a;
    constant = b;
    evalFlag_ = false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    BigInteger zero = new BigInteger("0");
    Expr zilch = factory_.createNumExpr(zero);
    Mode m = null;
    boolean[] inputs = new boolean[1];
    double solutions;
    if( (env.isDefined(args[0])) ) {
      inputs[0] = true;
      solutions = 0.5;
      m = new Mode(env,inputs,solutions);
    }
    else {
      inputs[0] = false;
      solutions = 1.0;
      env = env.add(args[0],null);
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
        if (evalMode_.isInput(0)) {
          evalFlag_ = false;
          Expr a = evalMode_.getEnvir().lookup(args[0]);
          if(a.equals(constant))
            result = true;
          }
        else {
          evalFlag_ = false;
          evalMode_.getEnvir().setValue(args[0],constant);
          result = true;
        }
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatConstVisitor) {
      FlatConstVisitor v = (FlatConstVisitor) visitor;
      return v.visitFlatConst(this);
    }
    return super.accept(visitor);
  }

  public /*@non_null@*/ Object[] getChildren()
  {
    Object[] result = { args[0], constant };
    return result;
  }

  public Term create(Object[] children)
  {
    try {
      RefName a = (RefName) children[0];
      Expr b = (Expr) children[1];
      return new FlatConst(a, b);
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
  }
}
