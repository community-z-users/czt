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
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** A simple implementation of a set comprehension.
 *  When this is created, the precise values of all
 *  free variables are known and are in the given environment.
 *
 * @author marku
 *
 */
public class SetComp extends DefaultEvalSet
{
  private static final Logger LOG =
    Logger.getLogger("net.sourceforge.czt.animation.eval.result");
  
  /** This FlatPredList is used to evaluate ALL members of the set. */
  protected FlatPredList preds_;

  /** This is the environment that defines all the free variables
   *  of this set comprehension.
   */
  protected Envir env0_;

  /** This stores general information about the bounds of the variables
   *  in this set comprehension.  Note that these bounds hold for ALL
   *  elements of the set, so any bounds analysis for particular
   *  members must not modify these Bounds.
   */
  protected Bounds bounds_;

  /** The generated environment that contains the output values.
   *  When this is non-null, it means that we are in the process
   *  of lazily evaluating the members of the set.
   */
  protected Envir outputEnvir_ = null;

  protected double estSize_ = UNKNOWN_SIZE;

  /** The fresh ZName which will be bound to a member of the set. */
  protected ZName resultName_;

  /** The resultName must be for predsAll. */
  public SetComp(FlatPredList preds, ZName resultName,
      Envir env0, Bounds bnds)
  {
    preds_ = preds;
    env0_ = env0;
    resultName_ = resultName;
    bounds_ = new Bounds(bnds);
    bounds_.startAnalysis(bnds);
    // infer bounds for the free vars, whose values are now known.
    for (ZName free : preds.freeVars()) {
      if ( ! free.equals(resultName_)) {
        Expr value = env0.lookup(free);
        //System.out.println("add bounds for "+free+" = "+val);
        // value may be null if this set is being used from chooseMode
        if (value != null) {
          bounds_.addConst(free, value);
        }
      }
    }
    preds_.inferBoundsFixPoint(bounds_);
    bounds_.endAnalysis();
    //System.out.println("setComp bounds = "+bounds_);
    //System.out.println("predsAll_ free= "+preds_.freeVars()+", "+preds_);
    // try to estimate its size.
    Mode m = preds_.chooseMode(env0_);
    if (m != null) {
      estSize_ = m.getSolutions();
      // TODO: infer maxSize here???
    }
  }

  @Override
  public BigInteger maxSize()
  {
    return super.maxSize();
  }

  @Override
  public double estSize()
  {
    return estSize_;
  }

  @Override
  public boolean contains(Object e)
  {
    if ( ! (e instanceof Expr)) {
      String msg = "illegal non-Expr object " + e + " cannot be in " + this;
      throw new RuntimeException(msg);
    }
    // Add the expected answer to the environment.
    // This allows the predicates inside the set to CHECK the result
    // rather than generating all possible results.
    Envir env = env0_.plus(resultName_, (Expr)e);
    // now do some additional static inference for this member.
    // TODO: find out why this *weakens* bounds_
    //Bounds ebnds = new Bounds(bounds_);
    //addBounds(preds_, ebnds, resultName_, (Expr)e);
    Mode m = preds_.chooseMode(env); // TODO: try doing this at constructor time?
    if (m == null)
      throw new EvalException("Cannot even test member of SetComp: " + this);
    preds_.setMode(m);
    preds_.startEvaluation();
    return preds_.nextEvaluation();
  }

  @Override
  public Expr nextMember()
  {
    if (outputEnvir_ == null) {
      Mode m = preds_.chooseMode(env0_);
      if (m == null)
        throw new EvalException("Cannot generate members of SetComp: " + this);
      preds_.setMode(m);
      preds_.startEvaluation();
      outputEnvir_ = preds_.getOutputEnvir();
    }
    if (preds_.nextEvaluation())
      return outputEnvir_.lookup(resultName_);
    else
      return null;
  }

  @Override
  public Iterator<Expr> matchIterator(Map<Object, Expr> argValues)
  {
    LOG.entering("SetComp", "matchIterator", argValues);
    // Add the expected args of resultName_ so that the enumeration
    // of members sees that those args are already known.
    Map<Object, ZName> argNames = bounds_.getStructure(resultName_);
    if (argNames == null) {
      LOG.exiting("SetComp", "matchIterator", "using normal iterator()");
      return iterator();  // no known aliasing
    }
    else {
      Envir env = env0_;
      // add the known argument values to the initial environment
      for (Entry<Object, Expr> argValue : argValues.entrySet()) {
        LOG.fine("adding "+argValue.getKey()
            +": "+argNames.get(argValue.getKey())
            +" = "+argValue.getValue());
        env = env.plus(argNames.get(argValue.getKey()), argValue.getValue());
      }
      /*
      ebnds.startAnalysis(bounds_);
      if (e instanceof NumExpr) {
        // TODO: make this code common with FlatConst.
        BigInteger val = ((NumExpr)e).getValue();
        ebnds.addLower(resultName_,val);
        ebnds.addUpper(resultName_,val);
      }
      if (e instanceof EvalSet) {
        ebnds.setEvalSet(resultName_, (EvalSet) e);
      }
      predsOne_.inferBoundsFixPoint(ebnds);
      ebnds.endAnalysis();
      */
      Mode m = preds_.chooseMode(env);
      if (m == null)
        throw new EvalException("Cannot generate matching members ("
            +argValues+"\n    of SetComp: " + this);
      preds_.setMode(m);
      preds_.startEvaluation();
      LOG.fine("starting to enumerate matching members with mode "+m);

      // TODO: find a nicer way of returning the set without enumerating
      //   all solutions first.  Perhaps the result should be an EvalSet?

      // put all evaluation results into a discrete set
      EvalSet result = new DiscreteSet();
      Envir outputEnv = preds_.getOutputEnvir();
      while (preds_.nextEvaluation()) {
        Expr value = outputEnv.lookup(resultName_);
        LOG.finer("found member="+value);
        result.add(value);
      }
      LOG.exiting("SetComp", "matchIterator",
          "iterator through " + result.estSize() + " matching members");
      return result.iterator();
    }
  }

  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("{ ");
    result.append(preds_.toString());
    result.append(" @ ");
    result.append(resultName_.toString());
    result.append(" }");
    return result.toString();
  }
}
