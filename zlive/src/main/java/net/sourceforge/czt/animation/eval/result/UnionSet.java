/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.result;

import java.math.BigInteger;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.Expr;

/** A simple implementation of the union of two EvalSets.
 *
 * @author marku
 *
 */
public class UnionSet extends DefaultEvalSet
{
  /** The left-hand EvalSet. */
  private EvalSet leftSet_;

  /** The right-hand EvalSet. */
  private EvalSet rightSet_;

  /** The iterator used by nextMember. */
  private Iterator<Expr> iter_;

  /** TODO: could combine/simplify some sets rather than creating union.
   *  For example, we could combine \{2\} and 3..+infinity, giving 2..+infinity.
   * @param left
   * @param right
   */
  public UnionSet(EvalSet left, EvalSet right)
  {
    leftSet_ = left;
    rightSet_ = right;
    iter_ = new UnionSetIterator();
  }

  @Override
  public BigInteger maxSize()
  {
    BigInteger leftMax = leftSet_.maxSize();
    BigInteger rightMax = rightSet_.maxSize();
    if (leftMax == null || rightMax == null)
      return null;
    else
      return leftMax.add(rightMax);
  }

  @Override
  public double estSize()
  {
    return leftSet_.estSize() + rightSet_.estSize();
  }

  @Override
  public boolean contains(Object obj)
  {
    return leftSet_.contains(obj) || rightSet_.contains(obj);
  }

  /** Calculates minimum of all the elements.
   *  Returns null if the set does not contain integers,
   *  or if it is empty.
   */
  @Override
  public BigInteger getLower()
  {
    BigInteger leftLower = leftSet_.getLower();
    BigInteger rightLower = rightSet_.getLower();
    if (leftLower == null || rightLower == null)
      return null;
    else
      return leftLower.min(rightLower);
  }

  /** Calculates maximum of all the elements.
   *  Returns null if the set does not contain integers,
   *  or if it is empty.
   */
  @Override
  public BigInteger getUpper()
  {
    BigInteger leftUpper = leftSet_.getUpper();
    BigInteger rightUpper = rightSet_.getUpper();
    if (leftUpper == null || rightUpper == null)
      return null;
    else
      return leftUpper.max(rightUpper);
  }

  @Override
  protected Expr nextMember()
  {
    if (iter_.hasNext())
      return iter_.next();
    else
      return null;
  }

  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(leftSet_.toString());
    result.append(" u ");
    result.append(rightSet_.toString());
    return result.toString();
  }

  /** This iterates through both sets.
   *  It may return duplicate expressions.
   */
  private class UnionSetIterator implements Iterator<Expr>
  {
    /** Used by next to iterate through both sets. */
    private Iterator<Expr> memberIterator_ = null;

    /** Used by next to know which set it is iterating through.
     *  1 means leftSet_, 2 means rightSet_
     */
    private int membersFrom_ = 0;

    /** This is the next Expr to be returned.
     *  Null means there are no more members.
     */
    private Expr nextExpr;

    public UnionSetIterator()
    {
      // now set up next to start iterating through leftSet_
      memberIterator_ = leftSet_.iterator();
      membersFrom_ = 1;
      nextExpr = findNext();
    }
    public boolean hasNext()
    {
      return nextExpr != null;
    }
    public Expr next()
    {
      Expr result = nextExpr;
      nextExpr = findNext();
      return result;
    }
    private Expr findNext()
    {
      while (memberIterator_ != null) {
        if (memberIterator_.hasNext())
          return memberIterator_.next();
        else if (membersFrom_ == 1) {
          memberIterator_ = rightSet_.iterator();
          membersFrom_++;
        }
        else {
          memberIterator_ = null;
          membersFrom_++;
        }
      }
      return null;
    }
    public void remove()
    {
      throw new UnsupportedOperationException(
          "The Remove Operation is not supported");
    }
  }
}
