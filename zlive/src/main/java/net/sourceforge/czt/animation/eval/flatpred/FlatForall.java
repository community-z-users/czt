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
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZNameComparator;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatForallVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.ZName;

public class FlatForall extends FlatPred
{
  protected static final Logger LOG
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  protected FlatPredList schText_;
  protected FlatPredList body_;

  protected Bounds schBounds_;
  protected Bounds bodyBounds_;

  /** The mode returned by schText_ */
  protected Mode schMode_ = null;

  /** The mode returned by body_ */
  protected Mode bodyMode_ = null;

  public FlatForall(FlatPredList sch, FlatPredList body)
  {
    LOG.entering("FlatForall","FlatForall");
    schText_ = sch;
    body_ = body;

    // freeVars_ := sch.freeVars + (body.freeVars - sch.boundVars)
    freeVars_ = new HashSet<ZName>(schText_.freeVars());
    //System.out.println("schText freevars = "+schText_.freeVars());
    //System.out.println("schText boundvars = "+schText_.boundVars());
    //System.out.println("body freevars = "+body_.freeVars());
    Set<ZName> bound = sch.boundVars();
    for (ZName var : body_.freeVars()) {
      if (var.getId() == null) {
        System.out.println("Warning: ZName "+var+" doesn't have an id.");
      }
      if ( ! bound.contains(var))
        freeVars_.add(var);
    }
    //System.out.println("freevars = "+freeVars_);
    args_ = new ArrayList<ZName>(freeVars_);
    Collections.sort(args_, ZNameComparator.create()); // so the order is reproducible
    solutionsReturned_ = -1;
    LOG.exiting("FlatForall","FlatForall");
  }

  /** This lets bound information flow into the
   *  quantifier, but not out.  This is because the constraints
   *  on the bound variables can be arbitrarily tight, and these
   *  should not be allowed to influence the bounds of any free variables.
   *  Similarly, bounds information can flow from the bound variables
   *  into the body of the quantifier, but not in the reverse direction.
   */
  public boolean inferBounds(Bounds bnds)
  {
    if (schBounds_ == null)
      schBounds_ = new Bounds(bnds);
    if (bodyBounds_ == null)
      bodyBounds_ = new Bounds(schBounds_);
    schBounds_.startAnalysis(bnds);
    schText_.inferBounds(schBounds_);
    bodyBounds_.startAnalysis(schBounds_);
    body_.inferBounds(bodyBounds_);
    bodyBounds_.endAnalysis();
    schBounds_.endAnalysis();
    return false;
  }

  /** Chooses the mode in which the predicate can be evaluated.
   *  @czt.todo Quantifiers are one place where it would be nice to
   *            have separate 'cost' and 'numSolutions' information
   *            within Mode objects, because the cost of evaluating a
   *            universal quantifier can be large, even though it returns
   *            only a single true or false solution.
   */
  public ModeList chooseMode(/*@non_null@*/ Envir env)
  {
    LOG.entering("FlatForall","chooseMode",env);
    LOG.fine("freevars="+freeVars_.toString());
    // Use modeAllDefined to check that all free variables are defined
    Mode mode = modeAllDefined(env);
    Mode schMode = null;
    Mode bodyMode = null;
    ModeList result = null;

    if (mode != null) {
      // Now check if the bound vars are finite enough to enumerate
      schMode = schText_.chooseMode(env);
      LOG.fine("schema text gives mode = " + schMode);
      if (schMode != null) {
        // Now check that the body of the quantifier can be evaluated.
        bodyMode = body_.chooseMode(schMode.getEnvir());
        LOG.fine("body gives mode: " + bodyMode);
      }
    }

    if (bodyMode != null) {
      // package schMode and bodyMode into a compound Mode
      result = new ModeList(mode);
      result.add(schMode);
      result.add(bodyMode);
    }

    LOG.exiting("FlatForall","chooseMode",result);
    return result;
  }

  public Set<ZName> freeVars()
  { return freeVars_; }

  //@ requires mode instanceof ModeList;
  public void setMode(/*@non_null@*/Mode mode)
  {
    super.setMode(mode);
    Iterator<Mode> submodes = ((ModeList)mode).iterator();
    schText_.setMode(submodes.next());
    body_.setMode(submodes.next());
    assert( ! submodes.hasNext());
  }

  public boolean nextEvaluation()
  {
    assert(evalMode_ != null);
    if (solutionsReturned_ == 0) {
      // start from the beginning of the list
      solutionsReturned_++;
      schText_.startEvaluation();
      while (schText_.nextEvaluation()) {
        body_.startEvaluation();
        // there must be (at least) one true solution from the body part
        if (!(body_.nextEvaluation())) {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  @Override
  public String toString()
  {
    return printQuant("(forall",
        schText_.toString(),
        body_.toString(),
        ")");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatForallVisitor)
      return ((FlatForallVisitor<R>) visitor).visitFlatForall(this);
    else
      return super.accept(visitor);
  }
}
