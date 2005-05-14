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

import java.util.*;
import java.util.logging.Logger;
import java.math.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;

public class FlatForall extends FlatPred
{
  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval.FlatForAll");

  private FlatPredList schText_;
  private FlatPredList body_;
  private Set/*<RefName>*/ freeVars_;
  
  /** The mode returned by schText_ */
  private Mode schMode_ = null;

  /** The mode returned by body_ */
  private Mode bodyMode_ = null;

  public FlatForall(FlatPredList sch, FlatPredList body)
  {
    schText_ = sch;
    body_ = body;

    // freeVars_ := sch.freeVars + (body.freeVars - sch.boundVars)
    freeVars_ = new HashSet(schText_.freeVars());
    Set/*<RefName>*/ bound = sch.boundVars();
    for (Object/*RefName*/ v : body_.freeVars()) {
      if ( ! bound.contains(v))
        freeVars_.add(v);
    }
    args = new ArrayList(freeVars_);
    solutionsReturned = -1;
  }

  /** Chooses the mode in which the predicate can be evaluated.
   *  @czt.todo Quantifiers are one place where it would be nice to 
   *            have separate 'cost' and 'numSolutions' information 
   *            within Mode objects, because the cost of evaluating a
   *            universal quantifier can be large, even though it returns
   *            only a single true or false solution.
   */
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    sLogger.entering("FlatForAll","chooseMode");
    // Use modeAllDefined to check that all free variables are defined
    Mode mode = modeAllDefined(env);
    if (mode != null) {
      // Now check if the bound vars are finite enough to enumerate
      mode = schText_.chooseMode(env);
      sLogger.fine("schema text gives mode = " + mode);
      if (mode != null) {
	// Now check that the body of the quantifier can be evaluated.
	mode = body_.chooseMode(mode.getEnvir());
	sLogger.fine("body gives mode: " + mode);
      }
    }
    // We return the body mode, which should have solutions <= 1.0.
    sLogger.exiting("FlatForAll","chooseMode",mode);
    return mode;
  }

  public Set freeVars()
  { return freeVars_; }

  public void startEvaluation()
  {
    sLogger.entering("FlatForAll","startEvaluation");
    assert(evalMode_ != null);
    super.startEvaluation();
    // TODO: store schMode_ & bodyMode_ within evalMode_ to avoid recalculation
    schMode_ = schText_.chooseMode(evalMode_.getEnvir());
    sLogger.fine("schMode_ = " + schMode_);
    schText_.startEvaluation(schMode_, evalMode_.getEnvir());
    bodyMode_ = body_.chooseMode(schMode_.getEnvir());
    sLogger.fine("bodyMode_ = " + bodyMode_);
    body_.startEvaluation(bodyMode_,schMode_.getEnvir());
    sLogger.exiting("FlatForAll","startEvaluation");
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    sLogger.entering("FlatForAll","nextEvaluation");
    assert(evalMode_ != null);
    assert(schMode_ != null);
    assert(bodyMode_ != null);
    Envir bodyEnv = schMode_.getEnvir();
    sLogger.fine("bodyEnv = " + bodyEnv);
    while (schText_.nextEvaluation()) {
      sLogger.finest("next gives bodyEnv = " + bodyEnv);
      body_.startEvaluation(bodyMode_,bodyEnv);
      if (!(body_.nextEvaluation())) {
	sLogger.exiting("FlatForAll","nextEvaluation",Boolean.FALSE);
        return false;
      }
    }
    sLogger.exiting("FlatForAll","nextEvaluation",Boolean.TRUE);
    return true;
  }


  public String toString() {
    StringBuffer result = new StringBuffer();
    // Start with the class name (in case it is a subclass).
    String fullName = this.getClass().getName();
    int dotPos = fullName.lastIndexOf('.') + 1; // -1 becomes 0.
    result.append(fullName.substring(dotPos));
    // Now add ( SchemaText @ Body )
    result.append("( ");
    result.append(schText_.toString());
    result.append(" @ ");
    result.append(body_.toString());
    result.append(" )");
    return result.toString();
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatForallVisitor) {
      FlatForallVisitor flatForallVisitor = (FlatForallVisitor) visitor;
      return flatForallVisitor.visitFlatForall(this);
    }
    return super.accept(visitor);
  }
}
