/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2007 Mark Utting

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

package net.sourceforge.czt.animation.eval;

import java.util.ListIterator;

import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;


public class ZLiveResult
{
  protected String section_;
  protected Term original_;
  protected Term unfolded_;
  protected FlatPredList code_;
  protected Term result_;

  /** An iterator through result_ (if it is an EvalSet) */
  protected ListIterator<Expr> currIter_ = null;

  /** The position in currSet of currMember_ (0 .. n+1).
   *  Invariant: this is always the value of currSet_.nextIndex() and
   *  currMember_ (if non-null) is always the value of currSet_.previous().
   */
  protected int currPosition_ = 0;

  /** The current member of currSet that has been shown. */
  protected Expr currMember_ = null;

  /** Record the result of an evaluation.
   *  All of the arguments must be non-null.
   * @param original  The term that was evaluated
   * @param unfolded  The term after preprocessing
   * @param code      The internal FlatPred code used during evaluation
   * @param result    The result of evaluation
   */
  public ZLiveResult(String section, Term original, Term unfolded,
      FlatPredList code, Term result)
  {
    this.section_ = section;
    this.original_ = original;
    this.unfolded_ = unfolded;
    this.code_ = code;
    this.result_ = result;
    if (result instanceof EvalSet) {
      currIter_ = ((EvalSet)result).listIterator();
    }
  }

  public boolean isExpr()
  {
    return result_ instanceof Expr;
  }

  public boolean isPred()
  {
    return result_ instanceof Pred;
  }

  public boolean isSet()
  {
    return result_ instanceof EvalSet;
  }

  public String getSectionName()
  {
    return section_;
  }

  public Term getOriginalTerm()
  {
    return original_;
  }

  public Term getUnfoldedTerm()
  {
    return unfolded_;
  }

  public FlatPredList getCode()
  {
    return code_;
  }

  public Term getResult()
  {
    return result_;
  }

  /** The position of the currentMember() in the current set.
   *  You should call this method only when isSet() is true.
   *  If this returns 0, then currentMember() will return null.
   *  @return 0 .. n, where n is the size of the current set.
   */
  public int currentPosition()
  {
    return currPosition_;
  }

  public Expr currentMember()
  {
    return currMember_;
  }

  /** Tries to move to member number 'position' in currSet.
   * @throws RuntimeException if the current result is not a set,
   *  if position is not positive, or if it is larger than the number
   *  of solutions in the current set.  Note that this steps sequentially
   *  through the set, so large values of position may take huge amounts
   *  of time.  However, once members of the set have been generated, they
   *  are cached, so traversing backwards and forwards is fine.
   */
  public void moveTo(int position)
  {
    if (currIter_ == null) {
      throw new RuntimeException("no current set or schema");
    }
    if (position <= 0) {
      throw new RuntimeException("no previous solutions");
    }
    else {
      while (position < currPosition_ && currIter_.hasPrevious()) {
        // step backwards
        currMember_ = currIter_.previous();
        currPosition_ = currIter_.nextIndex();
      }
      while (position > currPosition_ && currIter_.hasNext()) {
        // step forwards
        currMember_ = currIter_.next();
        currPosition_ = currIter_.nextIndex();
      }
      if (position > currPosition_) {
        throw new RuntimeException("no more solutions");
      }
    }
    // now display the current element
    if (currPosition_ > 0) {
      // make sure we have got the element just *before* currPosition_.
      currIter_.previous();
      currMember_ = currIter_.next();
      currPosition_ = currIter_.nextIndex();
    }
  }
}
