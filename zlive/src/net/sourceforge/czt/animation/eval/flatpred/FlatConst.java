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
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

/** FlatPlus implements the var = const predicate. */
public class FlatConst extends FlatPred
{
  protected Expr constant;
  private Factory factory_ = new Factory();
  
  public FlatConst(RefName a, Expr b)
  {
    args = new ArrayList(1);
    args.add(a);
    constant = b;
    solutionsReturned = -1;
  }

  //@ requires newargs.size() == 2;
  public FlatConst(ArrayList newargs)
  {
    if (newargs == null || newargs.size() != 2)
      throw new IllegalArgumentException("FlatConst requires 2 args");
    args = new ArrayList(1);
    args.add(newargs.get(0));
    constant = (Expr)newargs.get(1);
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
    if(solutionsReturned == 0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(0)) {
        Expr a = evalMode_.getEnvir().lookup((RefName)args.get(0));
        if(a.equals(constant))
          result = true;
      }
      else {
        evalMode_.getEnvir().setValue((RefName)args.get(0),constant);
        result = true;
      }
    }
    return result;
  }
  
  public String toString() {
    String val = "???";
    if (constant != null)
      val = constant.toString();
    if (constant instanceof NumExpr)
      val = ((NumExpr)constant).getValue().toString();
    return ("FlatConst(" + ((RefName)args.get(0)).toString() + "," + val + ")");
  }


  ///////////////////////// Pred methods ///////////////////////

  /** getChildren returns { args[0], constant } */
  public /*@non_null@*/ Object[] getChildren()
  {
    Object[] result = new Object[2];
    result[0] = args.get(0);
    result[1] = constant;
    return result;
  }

  public /*@non_null@*/ Term create(/*@non_null@*/ Object[] newargs)
  {
    return new FlatConst((RefName)newargs[0], (Expr)newargs[1]);
  }
 
  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatConstVisitor) {
      FlatConstVisitor v = (FlatConstVisitor) visitor;
      return v.visitFlatConst(this);
    }
    return super.accept(visitor);
  }
}
