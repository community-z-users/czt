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

import java.util.ArrayList;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatConstVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNumeral;
import net.sourceforge.czt.z.util.PrintVisitor;

/** FlatPlus implements the var = const predicate. */
public class FlatConst extends FlatPred
{
  protected Expr constant_;
  
  public FlatConst(ZName a, Expr b)
  {
    args_ = new ArrayList<ZName>(1);
    args_.add(a);
    constant_ = b;
    solutionsReturned_ = -1;
  }

  public boolean inferBounds(Bounds bnds)
  {
    bnds.addConst(args_.get(0), constant_);
    return false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    Mode m = modeOneOutput(env);
    // set the value of the constant now to improve later analysis
    // (note that when m!=null => args.get(0) is defined,
    //   but a null value means that its value is unknown)
    if (m != null && m.getEnvir().lookup(args_.get(0)) == null)
      m.getEnvir().setValue(args_.get(0), constant_);
    return m;
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert(evalMode_ != null);
    assert(solutionsReturned_ >= 0);
    boolean result = false;
    if(solutionsReturned_ == 0)
    {
      solutionsReturned_++;
      if (evalMode_.isInput(args_.get(0))) {
        Expr a = evalMode_.getEnvir().lookup(args_.get(0));
        if(a.equals(constant_))
          result = true;
      }
      else {
        evalMode_.getEnvir().setValue(args_.get(0),constant_);
        result = true;
      }
    }
    return result;
  }
  
  public String toString()
  {
    PrintVisitor printer = new PrintVisitor(false);
    String val = "-";   // means const value is not known yet
    if (constant_ != null)
      val = constant_.accept(printer);
    if (constant_ instanceof NumExpr) {
      NumExpr numExpr = (NumExpr) constant_;
      ZNumeral num = numExpr.getZNumeral();
      val = num.getValue().toString();
    }
    return printArg(0) + " == " + val;
  }


  ///////////////////////// Pred methods ///////////////////////

  /** getChildren returns { args[0], constant } */
  public /*@non_null@*/ Object[] getChildren()
  {
    Object[] result = new Object[2];
    result[0] = args_.get(0);
    result[1] = constant_;
    return result;
  }

  public /*@non_null@*/ FlatConst create(/*@non_null@*/ Object[] newargs)
  {
    return new FlatConst((ZName)newargs[0], (Expr)newargs[1]);
  }
 
  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatConstVisitor) {
      return ((FlatConstVisitor<R>) visitor).visitFlatConst(this);
    }
    return super.accept(visitor);
  }
}
