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
import net.sourceforge.czt.animation.eval.flatpred.Mode;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;


public class ZLiveResult
{
  protected String section_;  // always non-null
  protected Term original_;  // always non-null
  protected Term unfolded_;
  protected Envir envir0_;
  protected FlatPredList code_;
  protected ZName resultName_;
  protected Mode mode_;
  protected Term result_;

  /** An iterator through result_ (if it is an EvalSet) */
  protected ListIterator<Expr> currIter_ = null;

  /** The position in currIter_ of currMember_ (0 .. n, for an n-element set)
   *  Invariant: currPosition_ is always the value of currIter_.nextIndex() and
   *  currMember_ (if non-null) is always the value of currIter_.previous().
   *
   *  So currPosition_==0 means we are *before* the first element,
   *  and currMember_==null.
   *
   *  For a non-empty set of size n, the maximum value of currPosition_ is
   *  n, with currMember_ being the last element.
   */
  protected int currPosition_ = 0;

  /** The current member of currSet that has been shown. */
  protected Expr currMember_ = null;

  /** Convenience constructor that records all information
   *  about the evaluated term.
   *
   *  All of the arguments must be non-null.
   * @param original  The term that was evaluated
   * @param unfolded  The term after preprocessing
   * @param code      The internal FlatPred code used during evaluation
   * @param result    The result of evaluation
   */
  public ZLiveResult(String section, Term original,
      Envir env0, Term unfolded,
      FlatPredList code, ZName resultName, Mode mode,
      Term result)
  {
    this(section, original);
    this.setEnvir0(env0);
    this.setUnfoldedTerm(unfolded);
    this.setCode(code, resultName);
    this.setMode(mode);
    this.setResult(result);
  }

  /** Record the result of an evaluation.
   *
   * @param section   The section this term is relative to.
   * @param original  The term to be evaluated.
   */
  public ZLiveResult(String section, Term original)
  {
    assert section != null;
    assert original != null;
    this.section_ = section;
    this.original_ = original;
  }

  public boolean isExpr()
  {
    return original_ instanceof Expr;
  }

  public boolean isPred()
  {
    return original_ instanceof Pred;
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

  /** Record the result of flattening/simplifying the term.
   *
   * @param code Must be non-null.
   */
  public void setUnfoldedTerm(Term term)
  {
    assert term != null;
    unfolded_ = term;
  }

  public Envir getEnvir0()
  {
    return envir0_;
  }

  /** Record the initial environment in which the term is evaluated.
   *
   * @param env0 Must be non-null.
   */
  public void setEnvir0(Envir env0)
  {
    assert env0 != null;
    envir0_ = env0;
  }

  public FlatPredList getCode()
  {
    return code_;
  }

  public ZName getResultName()
  {
    return resultName_;
  }

  /** Record the result of compiling the flattened term.
   *
   * @param code Must be non-null.
   * @param resultName Must be non-null for expressions, null for predicates.
   */
  public void setCode(FlatPredList code, ZName resultName)
  {
    assert code != null;
    assert isExpr() == (resultName != null);
    code_ = code;
    resultName_ = resultName;
  }

  /** The mode that was used to evaluate the term. */
  public Mode getMode()
  {
    return mode_;
  }

  /** Record the mode that was used to evaluate the term.
   *
   * @param mode Must be non-null and use the same initial environment.
   */
  public void setMode(Mode mode)
  {
    assert mode != null;
    assert mode.getEnvir0() == this.getEnvir0() : ""+ mode.getEnvir0() +"=="+ this.getEnvir0();
    mode_ = mode;
  }

  public Term getResult()
  {
    return result_;
  }

  /** Set the result of evaluating the term.
   *
   * @param result Must be non-null.
   */
  public void setResult(Term result)
  {
    assert result != null;
    result_ = result;
    if (result instanceof EvalSet) {
      currIter_ = ((EvalSet)result).listIterator();
    }
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
    //System.out.println("moveTo("+position+") starts with currPos="
    //    + currPosition_ + " and iter.nextIndex()=" + currIter_.nextIndex());
    if (position <= 0) {
      throw new MoveException("no previous solutions");
    }
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
      throw new MoveException("no more solutions");
    }
    if (position < currPosition_) {
      throw new MoveException("no previous solutions");
    }
    assert currPosition_ == position;
    // now display the current element
    // make sure we have got the element just *before* currPosition_.
    assert currIter_.hasPrevious();
    currIter_.previous();
    currMember_ = currIter_.next();
    currPosition_ = currIter_.nextIndex();
    assert currPosition_ == position; // should be unchanged
  }

  /** An exception for the ZLiveResult move method.
   *  This is thrown when an impossible move is requested.
   *  For example, when the move attempts to move off the end or
   *  the beginning of the set.
   * @author marku
   */
  public static class MoveException extends net.sourceforge.czt.util.CztException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -6311708604178211492L;

	public MoveException(String msg) {
      super(msg);
    }
  }
}
