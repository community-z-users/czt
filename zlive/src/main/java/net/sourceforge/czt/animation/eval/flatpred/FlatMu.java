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
import net.sourceforge.czt.animation.eval.flatvisitor.FlatMuVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** This overrides the forall evaluation algorithm. */
public class FlatMu extends FlatPred
{
  protected static final Logger LOG
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  protected FlatPredList schText_;
  protected Bounds schBounds_;
  protected ZName resultName_;
  
  public FlatMu(FlatPredList sch, ZName result)
  {
    LOG.entering("FlatMu","FlatMu");
    schText_ = sch;
    resultName_ = result;
    freeVars_ = new HashSet<ZName>(schText_.freeVars());
    freeVars_.add(result);
    // HashSet has removed duplicates
    args_ = new ArrayList<ZName>(freeVars_);
    // move resultName_ to the end of args.
    args_.remove(resultName_);
    args_.add(resultName_);
    solutionsReturned_ = -1;
    LOG.exiting("FlatMu","FlatMu");
  }

  /** This does local bounds inference.
   *  So bounds information flows into the mu term, but not out.
   */
  public boolean inferBounds(Bounds bnds)
  {
    if (schBounds_ == null)
      schBounds_ = new Bounds(bnds);
    schBounds_.startAnalysis(bnds);
    schText_.inferBounds(schBounds_);
    schBounds_.endAnalysis();
    return false;
  }

  /** Allows functional modes (IIO and III).
   */
  public Mode chooseMode(/*@non_null@*/ Envir env0)
  {
    LOG.entering("FlatMu","chooseMode",env0);
    Mode mode = this.modeFunction(env0);
    if (mode != null) {
      Envir insideEnv = env0;
      if (mode.isInput(resultName_)) {
    	insideEnv = env0.hide(resultName_);
        // Note: we implement the III mode as IIO followed by an equals check.
        // For example, (\mu x:0..10 @ x) = 3
        // would give the wrong results if it is transformed into
        // (\mu x:0..10 @ 3).  So the III mode is not sound.
    	// So we avoid it by hiding resultName_ before passing the env to schText_.
      }
      // Now check if the bound vars are finite enough to enumerate
      Mode schmode = schText_.chooseMode(insideEnv);
      LOG.fine("schema text gives mode = " + mode);
      if (schmode == null)
        mode = null;  // cannot evaluate the FlatMu.
      else {
        ModeList finalMode = new ModeList(mode);
        finalMode.add(schmode);
        mode = finalMode;
      }
    }
    LOG.exiting("FlatMu","chooseMode",mode);
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
        if (value == null) {
          value = nextValue;
        }
        else if ( ! value.equals(nextValue)) {
          UndefException ex
            = new UndefException("Mu expression has multiple results: "
                + value + "  /=  " + nextValue);
          throw ex;
        }
      }
      if (value == null) {
        UndefException ex =
          new UndefException("Mu expression has no solutions: " + this);
        throw ex;
      }
      if (evalMode_.isInput(resultName_)) {
        if (value.equals(env.lookup(resultName_)))
          result = true;
      }
      else {
        env.setValue(resultName_, value);
        result = true;
      }
    }
    return result;
  }

  @Override
  public String toString() {
    return printQuant("(mu", schText_.toString(), printName(resultName_), ")");
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
