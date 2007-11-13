/**
 Copyright (C) 20067 Mark Utting
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
import net.sourceforge.czt.animation.eval.ZNameComparator;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatIfThenElseVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.ZName;

/**
 * FlatIfThenElse(p, e1, e2) implements IF p THEN e1 ELSE e2.
 * It requires all free vars of p to be ground.
 * It evaluates p to true or false, then returns one solution
 * from either e1 (when p is true) or e2 (when p is false).
 * The two FlatPredLists e1 and e2 must have identical modes
 * and should assign their evaluated result to the same name.
 * 
 * This implementation of IF-THEN-ELSE is quite similar to FlatOr, 
 * but here the two expressions cannot return multiple solutions, 
 * whereas in FlatOr each predicate may have any number of solutions.
 *
 * @author marku
 */
public class FlatIfThenElse extends FlatPred
{
  /** Bounds information for the left_ predicate. */
  protected Bounds leftBounds_;

  /** Bounds information for the right_ predicate. */
  protected Bounds rightBounds_;

  /** The predicate that controls the choice. */
  protected FlatPredList pred_;
  
  /** The left-hand expr, once known. */
  protected FlatPredList left_;

  /** The right-hand expr, once known. */
  protected FlatPredList right_;

  /** Creates a new instance of FlatUnion. */
  public FlatIfThenElse(FlatPredList pred, FlatPredList left, FlatPredList right)
  {
    super();
    pred_ = pred;
    left_ = left;
    right_ = right;
    freeVars_ = new TreeSet<ZName>(ZNameComparator.create());
    freeVars_.addAll(pred_.freeVars());
    freeVars_.addAll(left_.freeVars());
    freeVars_.addAll(right_.freeVars());
    args_ = new ArrayList<ZName>(freeVars_);
    solutionsReturned_ = -1;
  }

  /** Bounds information can only flow into the two expressions at the moment.
   */
  public boolean inferBounds(Bounds bnds)
  {
    // infer bounds on left side
    if (leftBounds_ == null)
      leftBounds_ = new Bounds(bnds);
    leftBounds_.startAnalysis(bnds);
    pred_.inferBounds(leftBounds_); // in the THEN part, we know pred_ is true.
    left_.inferBounds(leftBounds_);
    leftBounds_.endAnalysis();

    // infer bounds on right side
    if (rightBounds_ == null)
      rightBounds_ = new Bounds(bnds);
    rightBounds_.startAnalysis(bnds);
    right_.inferBounds(rightBounds_);
    rightBounds_.endAnalysis();

    return false;
  }

  public Mode chooseMode(Envir env0)
  {
    Mode result = null;
    Mode predMode = pred_.chooseMode(env0);
    if (predMode.numOutputs() > 0) {
      return null;
    }
    Mode leftMode = left_.chooseMode(env0);
    Mode rightMode = right_.chooseMode(env0);
    if (leftMode != null && rightMode != null
        && leftMode.compatible(rightMode)) {
      double solutions = Math.max(leftMode.getSolutions(), rightMode.getSolutions());
      List<Mode> modes = new ArrayList<Mode>(3);
      modes.add(predMode);
      modes.add(leftMode);
      modes.add(rightMode);
      Envir env = rightMode.getEnvir();
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
      pred_.startEvaluation();
      if (pred_.nextEvaluation()) {
        left_.startEvaluation();
        result = left_.nextEvaluation();
      }
      else {
        right_.startEvaluation();
        result = right_.nextEvaluation(); 
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
      + "\n)";
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
