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
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.util.Factory;

/** FlatNegate implements the -a = b predicate. */
public class FlatNegate extends FlatPred
{
  private Factory factory_ = new Factory();

  public FlatNegate(ZRefName a, ZRefName b)
  {
    args = new ArrayList<ZRefName>(2);
    args.add(a);
    args.add(b);
    solutionsReturned = -1;
  }

  public boolean inferBounds(Bounds bnds)
  {
    boolean changed = false;
    ZRefName a = args.get(0);
    ZRefName b = args.get(1);

    BigInteger aLower = bnds.getLower(a);
    BigInteger aUpper = bnds.getUpper(a);
    BigInteger bLower = bnds.getLower(b);
    BigInteger bUpper = bnds.getUpper(b);

    // propagate bounds from a to b.
    if (aUpper != null)
      changed |= bnds.addLower(b, aUpper.negate());
    if (aLower != null)
      changed |= bnds.addUpper(b, aLower.negate());

    // propagate bounds from b to a.
    if (bUpper != null)
      changed |= bnds.addLower(a, bUpper.negate());
    if (bLower != null)
      changed |= bnds.addUpper(a, bLower.negate());

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
    assert(solutionsReturned >= 0);
    boolean result = false;
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      if (evalMode_.isInput(0) && evalMode_.isInput(1)) {
        Expr a = evalMode_.getEnvir().lookup(args.get(0));
        Expr b = evalMode_.getEnvir().lookup(args.get(1));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = ((NumExpr)b).getValue();
        if(x.negate().equals(y))
          result = true;
      }
      else if (evalMode_.isInput(0)) {
        Expr a = evalMode_.getEnvir().lookup(args.get(0));
        BigInteger x = ((NumExpr)a).getValue();
        BigInteger y = x.negate();
        Expr b = factory_.createNumExpr(y);
        evalMode_.getEnvir().setValue(args.get(1),b);
        result = true;
      }
      else if (evalMode_.isInput(1)) {
        Expr b = evalMode_.getEnvir().lookup(args.get(1));
        BigInteger y = ((NumExpr)b).getValue();
        BigInteger x = y.negate();
        Expr a = factory_.createNumExpr(x);
        evalMode_.getEnvir().setValue(args.get(0),a);
        result = true;
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatNegateVisitor) {
      FlatNegateVisitor flatPlusVisitor = (FlatNegateVisitor) visitor;
      return flatPlusVisitor.visitFlatNegate(this);
    }
    return super.accept(visitor);
  }
}
