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

/** This overrides the forall evaluation algorithm. */
public class FlatMu extends FlatPred
{
  protected static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  protected FlatPredList schText_;
  private Set<ZRefName> freeVars_;
  
  public FlatMu(FlatPredList sch, ZRefName result)
  {
    sLogger.entering("FlatForall","FlatForall");
    schText_ = sch;
    freeVars_ = schText_.freeVars();
    args = new ArrayList<ZRefName>(freeVars_);
    solutionsReturned = -1;
    sLogger.exiting("FlatForall","FlatForall");
  }

  /** TODO */
  public boolean inferBounds(Bounds bnds)
  {
    return false;
  }

  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    sLogger.entering("FlatForall","chooseMode",env);
    // Use modeAllDefined to check that all free variables are defined
    Mode mode = modeAllDefined(env);

    if (mode != null) {
      // Now check if the bound vars are finite enough to enumerate
      mode = schText_.chooseMode(env);
      sLogger.fine("schema text gives mode = " + mode);
      }

    sLogger.exiting("FlatForall","chooseMode",mode);
    return mode;
  }

  /** TODO: Does the actual evaluation */
  public boolean nextEvaluation()
  {
    sLogger.entering("FlatExists","nextEvaluation");

    sLogger.exiting("FlatExists","nextEvaluation",Boolean.FALSE);
    return false;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    /* TODO
    if (visitor instanceof FlatMuVisitor) {
      FlatMuVisitor flatMuVisitor = (FlatMuVisitor) visitor;
      return flatMuVisitor.visitFlatMu(this);
    }
    */
    return super.accept(visitor);
  }
}
