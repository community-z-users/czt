/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004, 2006 Mark Utting

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

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatNotVisitor;
import net.sourceforge.czt.util.Visitor;

public class FlatNot extends FlatPredList
{
  protected Bounds bounds_;
  
  public FlatNot(ZLive zlive)
  {
    super(zlive);
  }

  /** This let bounds information flow into the negation, but not out. */
  public boolean inferBounds(Bounds bnds)
  {
    if (bounds_ == null)
      bounds_ = new Bounds(bnds);
    bounds_.startAnalysis(bnds);
    super.inferBounds(bounds_);
    bounds_.endAnalysis();
    return false;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public ModeList chooseMode(/*@non_null@*/ Envir env)
  {
    if (modeAllDefined(env) == null) return null;
    return super.chooseMode(env);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert(evalMode_ != null);
    if (solutionsReturned_ == 0) {
      return ! super.nextEvaluation();
    }
    return false;
  }


  ///////////////////////// Pred methods ///////////////////////

  public String toString() {
    String body = super.toString();
    if (body.contains("\n"))
      return "not (" + indent(body) + "\n)";
    else
      return "not (" + body + ")";
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatNotVisitor)
      return ((FlatNotVisitor<R>) visitor).visitFlatNot(this);
    else
      return super.accept(visitor);
  }
}
