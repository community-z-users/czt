/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.result;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.Set;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;

/** A simple implementation of {e1,e2,e3,...,eN}.
 *  A typical usage is to create it, add ALL the members,
 *  then release it to be used in other expressions.
 *  (If other expressions see it before all members are
 *  added, then the size and lower/upper bounds will be wrong).
 *
 * @author marku
 *
 */
public class SetComp extends EvalSet
{
  /** This FlatPredList is used to evaluate ALL members of the set. */
  protected FlatPredList predsAll_;

  /** This FlatPredList is used to check membership of ONE given value.
      Its first entry is resultNNN=value, where resultNNN is a fresh
      ZName (see resultName) and value is initially unknown, but will
      be set within the contains method before this FlatPredList is evaluated.
  */
  protected FlatPredList predsOne_;

  /** This is the environment that defines all the free variables
   *  of this set comprehension.
   */
  protected Envir env0_;

  /** The generated environment that contains the output values.
   *  When this is non-null, it means that we are in the process
   *  of lazily evaluating the members of the set.
   */
  protected Envir outputEnvir_ = null;

  protected double estSize_ = UNKNOWN_SIZE;
  
  /** The fresh ZName which will be bound to a member of the set. */
  protected ZName resultName_;
  
  public SetComp(FlatPredList predsAll, FlatPredList predsOne, ZName resultName, Envir env0)
  {
    predsAll_ = predsAll;
    predsOne_ = predsOne;
    env0_ = env0;
    resultName_ = resultName;
    // try to estimate its size.
    Mode m = predsAll_.chooseMode(env0_);
    System.out.println("SetComp mode returns "+m);
    if (m != null)
      estSize_ = m.getSolutions();
  }

  @Override
  public double estSize()
  {
    return estSize_;
  }

  @Override
  public boolean contains(Object e)
  {
    if ( ! (e instanceof Expr))
      throw new RuntimeException("illegal non-Expr object "+e+" cannot be in "+this);
    // Add the expected answer to the environment.
    // This allows the predicates inside the set to CHECK the result
    // rather than generating all possible results.
    Envir env = env0_.plus(resultName_, (Expr)e);
    // now do some additional static inference for this member.
    /*
    Bounds bnds = bounds_.clone();
    if (e instanceof NumExpr) {
      // TODO: make this code common with FlatConst.
      BigInteger val = ((NumExpr)e).getValue();
      bnds.addLower(resultName_,val);
      bnds.addUpper(resultName_,val);
    }
    predsOne_.inferBoundsFixPoint(bnds);
    */
    Mode m = predsOne_.chooseMode(env);
    if (m == null)
      throw new EvalException("Cannot even test member of SetComp: " + this);
    predsOne_.setMode(m);
    predsOne_.startEvaluation();
    return predsOne_.nextEvaluation();
  }

  @Override
  public Expr nextMember()
  {
    if (outputEnvir_ == null) {
      Mode m = predsAll_.chooseMode(env0_);
      if (m == null)
        throw new EvalException("Cannot generate members of SetComp: " + this);
      predsAll_.setMode(m);
      predsAll_.startEvaluation();
      outputEnvir_ = predsAll_.getOutputEnvir();
    }
    if (predsAll_.nextEvaluation())
      return outputEnvir_.lookup(resultName_);
    else
      return null;
  }
}
