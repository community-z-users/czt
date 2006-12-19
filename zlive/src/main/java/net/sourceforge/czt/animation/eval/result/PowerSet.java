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
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.z.ast.Expr;

/**
 * A power set with lazy evaluation of its elements.
 *
 * @author Petra Malik
 */
public class PowerSet extends DefaultEvalSet
{
  /** The base set, i.e. the set S, so that this represents Power(S). */
  private EvalSet baseset_;

  /** An iterator over all the elements of this set. */
  private PowerSetIterator iter_;

  /** Creates a new power set of the given base set. */
  public PowerSet(EvalSet baseset)
  {
    baseset_ = baseset;
  }

  /**
   * Power sets are never empty because they always contain the empty
   * set so this method always returns <code>false</code>.
   *
   * @return false.
   */
  public boolean isEmpty()
  {
    return false;
  }

  /** Returns the exact size of the set,
   *  or MAX_VALUE if the set is infinite or
   *  has cardinality greater than MAX_VALUE.
   */
  @Override
  public int size()
  {
    BigInteger size = maxSize();
    if (size == null ||
        size.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
      return Integer.MAX_VALUE;
    }
    return size.intValue();
  }

  /** Returns the exact size of the set, or
   *  null if it is infinite.
   */
  @Override
  public BigInteger maxSize()
  {
    BigInteger basesize = baseset_.maxSize();
    if (basesize == null  ||
        basesize.compareTo(BigInteger.valueOf(1000)) > 0) {
      return null;
    }
    return BigInteger.valueOf(2).pow(basesize.intValue());
  }

  /** This is the same as maxSize(), but converted to a double.
   *  So maxSize()==null gives Double.POSITIVE_INFINITY here.
   */
  @Override
  public double estSize()
  {
    BigInteger size = maxSize();
    if (size == null)
      return Double.POSITIVE_INFINITY;
    else
      return size.doubleValue();
  }

  /**
   * @throws EvalException if the given object is not an EvalSet.
   */
  @Override
  public boolean contains(Object e)
  {
    if ( !(e instanceof EvalSet)) {
      String msg = "Type error: members of PowerSet must be sets: " + e;
      throw new EvalException(msg);
    }
    EvalSet evalSet = (EvalSet) e;
    for (Expr expr : evalSet) {
      if (! baseset_.contains(expr)) {
        return false;
      }
    }
    return true;
  }

  @Override
  protected Expr nextMember()
  {
    if (iter_ == null) {
      iter_ = new PowerSetIterator(baseset_.iterator());
      return new DiscreteSet();
    }
    else if (iter_.hasNext()) {
      return iter_.next();
    }
    return null;
  }

  @Override
  protected void resetResult()
  {
    super.resetResult();
    iter_ = null;
  }

  public String toString()
  {
    return "Power (" + baseset_ + ")";
  }

  /**
   * An iterator over the elements of a non-empty power set of a given
   * base set.
   */
  protected class PowerSetIterator
  {
    private Iterator<Expr> baseIter_;
    private AddElementIterator addElemIter_;
    private int lengthOfList_ = 1;

    public PowerSetIterator(Iterator<Expr> baseIter)
    {
      baseIter_ = baseIter;
      if (baseIter_.hasNext()) {
        nextAddElementIterator();
      }
    }

    private void nextAddElementIterator()
    {
      addElemIter_ = new AddElementIterator(baseIter_.next(), memberList_,
                                            0, lengthOfList_);
      lengthOfList_ *= 2;
    }

    public boolean hasNext()
    {
      return baseIter_.hasNext() ||
        (addElemIter_ != null && addElemIter_.hasNext());
    }

    public DiscreteSet next()
    {
      if (addElemIter_ == null) throw new NoSuchElementException();
      if (addElemIter_.hasNext()) {
        return addElemIter_.next();
      }
      nextAddElementIterator();
      return addElemIter_.next();
    }
  }

  protected static class AddElementIterator
  {
    /** The List of sets to which an element is to be added. */
    private final List<Expr> list_;

    /** The expr to be added. */
    private final Expr expr_;

    /** The current position */
    private int pos_;

    /** The end position */
    private final int end_;;

    public AddElementIterator(Expr expr, List<Expr> list,
                              int start, int end)
    {
      expr_ = expr;
      list_ = list;
      pos_ = start;
      end_ = end;
    }

    public boolean hasNext()
    {
      return pos_ < end_;
    }

    public DiscreteSet next()
    {
      DiscreteSet result = new DiscreteSet();
      result.addAll(((Collection<Expr>) list_.get(pos_++)));
      result.add(expr_);
      return result;
    }
  }
}
