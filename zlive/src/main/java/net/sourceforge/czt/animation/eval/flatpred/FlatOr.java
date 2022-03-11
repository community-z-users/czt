/**
 Copyright (C) 2006 Mark Utting
 This file is part of the czt project.

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

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.ZNameComparator;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatOrVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.ZName;

/**
 * FlatOr(p, q) implements p \lor q.
 * It returns all the solutions from p, followed by all the solutions from q.
 * The two FlatPreds or FlatPredLists p and q must have identical modes.
 *
 * @author marku
 */
public class FlatOr extends FlatPred
{
  /** Bounds information for the left_ predicate. */
  protected Bounds leftBounds_;

  /** Bounds information for the right_ predicate. */
  protected Bounds rightBounds_;

  /** The left-hand predicate, once known. */
  private FlatPredList left_;

  /** The variables that are created by *both* sides.
   *  (This is known only after setMode).
   */
  protected Set<ZName> outputs_;
  
  /** The right-hand predicate, once known. */
  private FlatPredList right_;

  /** How we know which set we are iterating through.
   *  1 means left_, 2 means right_
   */
  private int from_ = 0;

  /** Creates a new instance of FlatOr.
   *  The left and right sides can have different sets of free
   *  variables (as well as different bound variables, obviously).
   *  However, chooseMode() will succeed only when both sides
   *  have the same set of output variables, so the differences in
   *  the freevar sets must be only in the input variables.
   */
  public FlatOr(FlatPredList left, FlatPredList right)
  {
    super();
    left_ = left;
    right_ = right;
    freeVars_ = new TreeSet<ZName>(ZNameComparator.create());
    freeVars_.addAll(left_.freeVars());
    freeVars_.addAll(right_.freeVars());
    args_ = new ArrayList<ZName>(freeVars_);
    solutionsReturned_ = -1;
  }

  /** Bounds information can only flow into the disjuncts at the moment.
   *  TODO: Allowing it to flow out requires taking the disjunction of the
   *  bounds of the two disjuncts.
   */
  public boolean inferBounds(Bounds bnds)
  {
    // infer bounds on left side
    if (leftBounds_ == null)
      leftBounds_ = new Bounds(bnds);
    leftBounds_.startAnalysis(bnds);
    left_.inferBounds(leftBounds_);
    leftBounds_.endAnalysis();

    // infer bounds on right side
    if (rightBounds_ == null)
      rightBounds_ = new Bounds(bnds);
    rightBounds_.startAnalysis(bnds);
    right_.inferBounds(rightBounds_);
    rightBounds_.endAnalysis();

    // TODO: propagate the union of the bounds into the parent.
    return false;
  }

  public Mode chooseMode(Envir env0)
  {
    Mode result = null;
    Mode leftMode = left_.chooseMode(env0);
    if (leftMode == null) {
      return null;
    }
    // It would be nice to give 'right_' some hints about which mode to choose here.
    // It has to choose the same mode as 'left_'.
    Mode rightMode = right_.chooseMode(env0);
    if (rightMode == null) {
      return null;
    }
    Set<ZName> leftVars = leftMode.getEnvir().definedSince(env0);
    leftVars.retainAll(left_.freeVars());  // discard bound vars
    // TODO: investigate why left_.boundVars_ is legal here --
    //       should be protected.
    Set<ZName> rightVars = rightMode.getEnvir().definedSince(env0);
    rightVars.retainAll(right_.freeVars()); // discard bound vars
    //System.err.println("Leftvars="+leftVars+", rightVars="+rightVars);
    if (leftVars.equals(rightVars)) {
      double solutions = leftMode.getSolutions() + rightMode.getSolutions();
      List<Mode> modes = new ArrayList<Mode>(2);
      modes.add(leftMode);
      modes.add(rightMode);
      // now create the output environment.
      Envir env = env0;
      for (ZName out : leftVars) {
        assert args_.contains(out);
        env = env.plus(out, null);
      }
      result = new ModeList(this, env0, env, args_, solutions, modes);
    }
    return result;
  }

  /** Set the mode that will be used to evaluate this list.
   *  @param mode Must be one of the modes returned previously by chooseMode.
   */
  //@ requires mode instanceof ModeList;
  //@ ensures evalMode_ == mode;
  public void setMode(/*@non_null@*/Mode mode)
  {
    super.setMode(mode);
    // and set the left_ and right_ modes.
    ModeList modes = (ModeList) mode;
    assert modes.size() == 2;
    Mode leftMode = modes.get(0);
    Mode rightMode = modes.get(1);
    left_.setMode(leftMode);
    right_.setMode(rightMode);
    outputs_ = leftMode.getEnvir().definedSince(leftMode.getEnvir0());
    // WAS: outputs_.removeAll(left_.boundVars_);
    // (but that only removed bound vars at the top level of the predicate,
    //  whereas retaining just freeVars also removes inner bound vars.
    //  For example, this happens with: (not P) or Q, when P has bound vars). 
    outputs_.retainAll(left_.freeVars());  // discard bound vars

    // Now double check that both sides have the same outputs
    Set<ZName> rOutputs = rightMode.getEnvir().definedSince(leftMode.getEnvir0());
    // WAS: rOutputs.removeAll(right_.boundVars_);
    rOutputs.retainAll(right_.freeVars());
    if (!rOutputs.equals(outputs_)) {
    	throw new EvalException("FlatOr outputs " + outputs_ + "  !=   " + rOutputs);
    }
  }

  public void startEvaluation()
  {
    super.startEvaluation();
    from_ = 0;
  }

  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    boolean result = false;
    Envir env = evalMode_.getEnvir();
    if (from_ == 0) {
      left_.startEvaluation();
      from_ = 1;
    }
    if (from_ == 1) {
      result = left_.nextEvaluation();
      if (result) {
        // copy outputs from left output env into the main output env.
        Envir leftEnv = left_.getOutputEnvir();
        for (ZName out : outputs_) {
          env.setValue(out, leftEnv.lookup(out));
        }
      }
      else {
        right_.startEvaluation();
        from_ = 2;
      }
    }
    if (from_ == 2) {
      result = right_.nextEvaluation();
      if (result) {
        // copy outputs from right output env into the main output env.
        Envir rightEnv = right_.getOutputEnvir();
        for (ZName out : outputs_) {
          env.setValue(out, rightEnv.lookup(out));
        }
      }
      else {
        from_ = 3;
      }
    }
    if (result)
      solutionsReturned_++;
    return result;
  }

  @Override
  public String toString()
  {
    return "( " + indent(left_.toString())
      + "\n) \\/ ( " + indent(right_.toString())
      + "\n)";
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatOrVisitor) {
      FlatOrVisitor<R> v = (FlatOrVisitor<R>) visitor;
      return v.visitFlatOr(this);
    }
    return super.accept(visitor);
  }
}
