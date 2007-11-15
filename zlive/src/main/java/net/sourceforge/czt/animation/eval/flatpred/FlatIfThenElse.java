/**
 Copyright (C) 2007 Mark Utting
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
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.ZNameComparator;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatIfThenElseVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
 * FlatIfThenElse(p, e1,n1, e2,n2, resultName) implements
 *    (p => n1=e1 and resultName=n1) and
 *    (not(p) => n2=e2 and resultName=n2)
 *
 * It requires all free vars of p, e1 and e2 to be ground.
 * This IF-THEN-ELSE uses three separate FlatPredLists (for p, e1, e2).
 * Given an input environment env0, it evaluates all of those
 * FlatPredLists using env0, and then extends env0 by binding
 * just resultName to the result of e1 (if p is true) or e2 (if p is false).
 *
 * This implementation of IF-THEN-ELSE is quite similar to FlatOr,
 * but here the two expressions cannot return multiple solutions,
 * whereas in FlatOr each predicate may have any number of solutions.
 *
 * @author marku
 */
public class FlatIfThenElse extends FlatPred
{
  /** The predicate that controls the choice. */
  protected FlatPredList pred_;

  /** The left-hand expr. */
  protected FlatPredList left_;
  /** The name that left_ binds its value to. */
  protected ZName leftResult_;
  /** Bounds information for the left_ expression. */
  protected Bounds leftBounds_;

  /** The right-hand expr, once known. */
  protected FlatPredList right_;
  /** The name that right_ binds its value to. */
  protected ZName rightResult_;
  /** Bounds information for the right_ expression. */
  protected Bounds rightBounds_;

  /** The name that the result of the whole IF-THEN-ELSE is bound to. */
  protected ZName wholeResult_;

  /** Creates a new instance of FlatUnion. */
  public FlatIfThenElse(FlatPredList pred,
      FlatPredList left, ZName leftResult,
      FlatPredList right, ZName rightResult,
      ZName wholeResult)
  {
    super();
    pred_ = pred;
    left_ = left;
    leftResult_ = leftResult;
    right_ = right;
    rightResult_ = rightResult;
    wholeResult_ = wholeResult;
    freeVars_ = new TreeSet<ZName>(ZNameComparator.create());
    freeVars_.addAll(pred_.freeVars());
    freeVars_.addAll(left_.freeVars());
    freeVars_.addAll(right_.freeVars());
    freeVars_.add(wholeResult_);
    args_ = new ArrayList<ZName>(freeVars_);
    solutionsReturned_ = -1;
  }

  /** Bounds information flows into pred_, left_ and right_, but not out.
   */
  public boolean inferBounds(Bounds bnds)
  {
    // infer bounds on left side (we know pred_ is true).
    if (leftBounds_ == null)
      leftBounds_ = new Bounds(bnds);
    leftBounds_.startAnalysis(bnds);
    pred_.inferBounds(leftBounds_);
    left_.inferBounds(leftBounds_);
    leftBounds_.endAnalysis();

    // infer bounds on right side (do NOT assume that pred_ is true)
    if (rightBounds_ == null)
      rightBounds_ = new Bounds(bnds);
    rightBounds_.startAnalysis(bnds);
    right_.inferBounds(rightBounds_);
    rightBounds_.endAnalysis();

    return false;
  }

  /** This requires pred_ and both of left_ and right_ expressions
   * to have valid modes, because in general, we may have to evaluate
   * both expressions.  For example {x:0..y @ IF x<5 THEN 0 ELSE 10}
   * (depending on y, this may use only the THEN expression, or both).
   */
  public Mode chooseMode(Envir env0)
  {
    Mode result = null;
    Mode predMode = pred_.chooseMode(env0);
    if (predMode == null || predMode.numOutputs() > 0) {
      return null;
    }
    Mode leftMode = left_.chooseMode(env0);
    assert leftMode.isOutput(leftResult_);
    Mode rightMode = right_.chooseMode(env0);
    assert rightMode.isOutput(rightResult_);
    if (leftMode != null && rightMode != null
        && leftMode.compatible(rightMode)) {
      double solutions = Math.max(leftMode.getSolutions(), rightMode.getSolutions());
      List<Mode> modes = new ArrayList<Mode>(3);
      modes.add(predMode);
      modes.add(leftMode);
      modes.add(rightMode);
      Envir env = env0;
      if ( ! env0.isDefined(wholeResult_)) {
        env = env0.plus(wholeResult_, null);
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
    pred_.setMode(modes.get(0));
    left_.setMode(modes.get(1));
    right_.setMode(modes.get(2));
  }

  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    boolean result = false;
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      Expr resultValue = null;
      pred_.startEvaluation();
      if (pred_.nextEvaluation()) {
        left_.startEvaluation();
        if (left_.nextEvaluation()) {
          resultValue = left_.getOutputEnvir().lookup(leftResult_);
        }
        if (resultValue == null) {
          throw new EvalException("THEN expression did not return a result");
        }
      }
      else {
        right_.startEvaluation();
        if (right_.nextEvaluation()) {
          resultValue = right_.getOutputEnvir().lookup(rightResult_);
        }
        if (resultValue == null) {
          throw new EvalException("ELSE expression did not return a result");
        }
      }
      Envir env = evalMode_.getEnvir();
      if (evalMode_.isOutput(wholeResult_)) {
        env.setValue(wholeResult_, resultValue);
        result = true;
      }
      else {
        result = env.lookup(wholeResult_).equals(resultValue);
      }
    }
    return result;
  }

  @Override
  public String toString()
  {
    return "(IF " + indent(pred_.toString())
      + "\nTHEN " + indent(left_.toString())
      + "\nELSE " + indent(right_.toString())
      + "\n) = "+ printName(wholeResult_);
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatIfThenElseVisitor) {
      FlatIfThenElseVisitor<R> v = (FlatIfThenElseVisitor<R>) visitor;
      return v.visitFlatIfThenElse(this);
    }
    return super.accept(visitor);
  }
}
