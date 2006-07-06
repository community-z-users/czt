/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

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
import java.util.HashSet;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.UndefException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;

/** This overrides the forall evaluation algorithm. */
public class FlatMu extends FlatPred
{
  protected static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  protected FlatPredList schText_;
  protected ZRefName resultName_;
  
  public FlatMu(FlatPredList sch, ZRefName result)
  {
    sLogger.entering("FlatMu","FlatMu");
    schText_ = sch;
    resultName_ = result;
    freeVars_ = new HashSet<ZRefName>(schText_.freeVars());
    // HashSet has removed duplicates
    args_ = new ArrayList<ZRefName>(freeVars_);
    args_.add(resultName_);
    freeVars_.add(resultName_); // result of the mu is also a free var.
    solutionsReturned_ = -1;
    sLogger.exiting("FlatMu","FlatMu");
  }

  /** This does local bounds inference.
   *  So bounds information flows into the mu term, but not out.
   */
  public boolean inferBounds(Bounds bnds)
  {
    schText_.inferBounds(bnds.clone());
    return false;
  }

  /** Allows functional modes (IIO and III).
   *  TODO: prove that Flatten will never use the III mode
   *    or disallow it in some way.  Because (\mu x:0..10 @ x) = 3
   *    will give the wrong results if it is transformed into
   *    (\mu x:0..10 @ 3).  So the III mode may not be sound.
   */
  public Mode chooseMode(/*@non_null@*/ Envir env0)
  {
    sLogger.entering("FlatMu","chooseMode",env0);
    Mode mode = this.modeFunction(env0);
    if (mode != null) {
      // Now check if the bound vars are finite enough to enumerate
      Mode schmode = schText_.chooseMode(env0);
      sLogger.fine("schema text gives mode = " + mode);
      if (schmode == null)
        mode = null;  // cannot evaluate the FlatMu.
      else {
        ModeList finalMode = new ModeList(mode);
        finalMode.add(schmode);
        mode = finalMode;
      }
    }
    sLogger.exiting("FlatMu","chooseMode",mode);
    // Note that we return the original mode, with solutions <= 1.0
    // because \mu expressions return only one value, even if their
    // schema part has multiple solutions.
    // For example:  (\mu x:1..10 @ 3).
    return mode;
  }

  public void setMode( /*@non_null@*/ Mode mode)
  {
    assert mode instanceof ModeList;
    super.setMode(mode);
    ModeList modelist = (ModeList) mode;
    schText_.setMode(modelist.iterator().next());
  }

  /** Iterates through all solutions to the schema text
   *  and the expression, checks that they are all equal,
   *  then returns that value.  It throws an UndefException
   *  if the schema text/expr evaluation does, or if there
   *  are no solutions or more than one (distinct) solution.
   */
  public boolean nextEvaluation()
  {
    sLogger.entering("FlatMu", "nextEvaluation");
    assert evalMode_ != null;
    boolean result = false;
    Envir env = evalMode_.getEnvir();
    Envir schEnv = ((ModeList)evalMode_).get(0).getEnvir();
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      Expr value = null;
      schText_.startEvaluation();
      while (schText_.nextEvaluation()) {
        Expr nextValue = schEnv.lookup(resultName_);
        sLogger.fine("FlatMu gets next value: "+nextValue);
        if (value == null) {
          value = nextValue;
        }
        else if ( ! value.equals(nextValue)) {
          UndefException ex
            = new UndefException("Mu expression has multiple results: "
                + value + "  /=  " + nextValue);
          sLogger.throwing("FlatMu","nextEvaluation",ex);
          throw ex;
        }
      }
      if (value == null) {
        UndefException ex =
          new UndefException("Mu expression has no solutions: " + this);
        sLogger.throwing("FlatMu","nextEvaluation",ex);
        throw ex;
      }
      if (evalMode_.isInput(args_.size()-1)) {
        if (value.equals(env.lookup(resultName_)))
          result = true;
      }
      else {
        env.setValue(resultName_, value);
        result = true;
      }
    }
    sLogger.exiting("FlatMu", "nextEvaluation", result);
    return result;
  }

  public String toString() {
    StringBuffer result = new StringBuffer();
    result.append("FlatMu(");
    result.append(schText_.toString());
    result.append(" @ ");
    result.append(resultName_);
    result.append(")");
    return result.toString();
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatMuVisitor)
      return ((FlatMuVisitor<R>) visitor).visitFlatMu(this);
    else
      return super.accept(visitor);
  }
}
