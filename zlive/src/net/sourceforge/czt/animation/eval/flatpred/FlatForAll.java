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

public class FlatForAll extends FlatPred
{
  private FlatPredList schText_;
  private FlatPredList body_;
  private Set unionSet_;

  public FlatForAll(FlatPredList sch, FlatPredList body)
  {
    schText_ = sch;
    body_ = body;
    unionSet_ = new HashSet(schText_.freeVars());
    unionSet_.addAll(body_.freeVars());
    args = new ArrayList(unionSet_);
    solutionsReturned = -1;
  }
  
  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  { return modeAllDefined(env); }
  
  public Set freeVars()
  { return unionSet_; }
  
  public void startEvaluation()
  {
    assert(evalMode_ != null);
    super.startEvaluation();
    schText_.startEvaluation(evalMode_,evalMode_.getEnvir());
    body_.startEvaluation(evalMode_,evalMode_.getEnvir());
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert(evalMode_ != null);
    while (schText_.nextEvaluation()) {
      body_.startEvaluation(evalMode_,evalMode_.getEnvir());
      if (!(body_.nextEvaluation()))
        return false;
    }
    return true;
  }


  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatForAllVisitor) {
      FlatForAllVisitor flatForAllVisitor = (FlatForAllVisitor) visitor;
      return flatForAllVisitor.visitFlatForAll(this);
    }
    return super.accept(visitor);
  }
}
