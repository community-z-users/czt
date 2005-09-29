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

/** FlatEquals implements the a = b predicate. */
public class FlatEquals extends FlatPred
{
  public FlatEquals(ZRefName a, ZRefName b)
  {
    args = new ArrayList<ZRefName>(2);
    args.add(a);
    args.add(b);
    solutionsReturned = -1;
  }

  /** Copies integer bounds from each arg to the other. */
  public boolean inferBounds(Bounds bnds)
  {
    boolean changed = false;
    ZRefName left = args.get(0);
    ZRefName right = args.get(1);

    // get all existing bounds, BEFORE we start adding bounds.
    BigInteger lmin = bnds.getLower(left);
    BigInteger lmax = bnds.getUpper(left);
    BigInteger rmin = bnds.getLower(right);
    BigInteger rmax = bnds.getUpper(right);

    // propagate bounds from left to right.
    if (lmin != null)
      changed |= bnds.addLower(right, lmin);
    if (lmax != null)
      changed |= bnds.addUpper(right, lmax);

    // propagate bounds from right to left.
    if (rmin != null)
      changed |= bnds.addLower(left, rmin);
    if (rmax != null)
      changed |= bnds.addUpper(left, rmax);

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
        if(a.equals(b))
          result = true;
      }
      else if (evalMode_.isInput(0)) {
        Expr a = evalMode_.getEnvir().lookup(args.get(0));
        evalMode_.getEnvir().setValue(args.get(1),a);
        result = true;
      }
      else if (evalMode_.isInput(1)) {
        Expr b = evalMode_.getEnvir().lookup(args.get(1));
        evalMode_.getEnvir().setValue(args.get(0),b);
        result = true;
      }
    }
    return result;
  }

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatEqualsVisitor) {
      return ((FlatEqualsVisitor) visitor).visitFlatEquals(this);
    }
    return super.accept(visitor);
  }
}
