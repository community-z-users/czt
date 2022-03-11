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

import net.sourceforge.czt.animation.eval.UndefException;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatExistsVisitor;
import net.sourceforge.czt.util.Visitor;

/** This implements the exists quantifier.
 *  It overrides the forall evaluation algorithm.
 */
public class FlatExists extends FlatForall
{
  protected Bounds bounds_;

  public FlatExists(FlatPredList sch, FlatPredList body)
  {
    super(sch,body);
  }

  /** This allows bounds information to flow into the Exists but not out.
   *  Within the Exists, bound information can flow in both directions
   *  between the bound variable constraints and the body of the Exists.
   */
  public boolean inferBounds(Bounds bnds)
  {
    if (bounds_ == null)
      bounds_ = new Bounds(bnds);
    bounds_.startAnalysis(bnds);
    schText_.inferBounds(bounds_);
    body_.inferBounds(bounds_);
    bounds_.endAnalysis();
    return false;
  }

  public boolean nextEvaluation()
  {
    LOG.entering("FlatExists","nextEvaluation");
    assert(evalMode_ != null);
    UndefException undef = null;
    if (solutionsReturned_ == 0) {
      solutionsReturned_++;
      schText_.startEvaluation();
      while (schText_.nextEvaluation()) {
        body_.startEvaluation();
        try {
          if (body_.nextEvaluation()) {
            LOG.exiting("FlatExists","nextEvaluation",Boolean.TRUE);
            return true;
          }
        }
        catch (UndefException e) {
          if (undef == null)
            undef = e; // remember first undef error.
          // and continue, in case we find a true.
        }
      }
      if (undef != null) {
        LOG.throwing("FlatExists", "nextEvaluation", undef);
        throw undef;
      }
    }
    LOG.exiting("FlatExists","nextEvaluation",Boolean.FALSE);
    return false;
  }

  @Override
  public String toString()
  {
    return printQuant("(exists",
        schText_.toString(),
        body_.toString(),
        ")");
  }

  ///////////////////////// Pred methods ///////////////////////

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatExistsVisitor)
      return ((FlatExistsVisitor<R>) visitor).visitFlatExists(this);
    else
      return super.accept(visitor);
  }
}
