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
import java.util.ListIterator;
import java.util.NoSuchElementException;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.util.Factory;

/** A simple implementation of lo..hi.
 *  However, one or both of the bounds may be missing,
 *  in which case they are negative/positive infinity.
 *
 * @author marku
 *
 */
public class RangeSet extends EvalSet
{
  /** The exact value of the lower bound, or null if not known. */
  protected BigInteger lower_;

  /** The exact value of the upper bound, or null if not known. */
  protected BigInteger upper_;

  /** The name of this RangeSet ("" if not known) */
  protected String name_;

  protected Factory factory_ = new Factory();

  /** Maximum number of next() solutions from the iterators.
   *  Zero means infinite.
   */
  private static int numIterSize_ = 10;

  /** The set of all integers. */
  public final static RangeSet integers = new RangeSet(null, null, "ints");

  public RangeSet(BigInteger lo, BigInteger up)
  {
    this(lo, up, "");
  }

  public RangeSet(BigInteger lo, BigInteger up, String name)
  {
    lower_ = lo;
    upper_ = up;
    name_ = name;
  }

  /**
   * @return The maximum number of integers we should iterate through.
   */
  public static int getNumIterSize()
  {
    return numIterSize_;
  }

  /** Set the maximum number of integer values we should iterate
   *  through before throwing an EvalException.
   * @param size The maximum number of integers
   */
  public static void setNumIterSize(int size)
  {
    numIterSize_ = size;
  }

  public static void setNumIterSize(String value)
  {
    setNumIterSize(Integer.valueOf(value));
  }

  /** true iff there is a lower bound and an upper bound. */
  public boolean isFinite()
  {
    return lower_ != null && upper_ != null;
  }

  /** true iff this range is empty.
   *  That is, if lower and upper bounds are both known
   *  (not infinite) and upper < lower.
   */
  public boolean isEmpty()
  {
    return isFinite() && upper_.compareTo(lower_) < 0;
  }

  /** Returns the exact size of the set,
   *  or MAX_VALUE if the set is infinite or
   *  has cardinality greater than MAX_VALUE.
   */
  public int size()
  {
    BigInteger size = maxSize();
    if (size == null || size.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0)
      return Integer.MAX_VALUE;
    else
      return size.intValue();
  }

  /** Returns the exact size of the set, or
   *  null if it is infinite.
   */
  @Override
  public BigInteger maxSize()
  {
    if (! isFinite())
      return null;
    if (isEmpty())
      return BigInteger.ZERO;
    else
      return upper_.subtract(lower_).add(BigInteger.ONE);
  }

  public boolean contains(Object e)
  {
     if ( !(e instanceof NumExpr))
       throw new EvalException("Type error: members of FlatRangeSet "
           + name_ + " must be numbers: " + e);
     BigInteger i = ((NumExpr)e).getValue();
     return (lower_ == null || lower_.compareTo(i) <= 0)
         && (upper_ == null || upper_.compareTo(i) >= 0);
   }

  public Iterator<Expr> iterator()
  {
      return listIterator();
  }

  /** Iterates from low to high if there is a lower bound,
   *  otherwise it iterates from high to low.  If there are
   *  no bounds, it will return an iterator that throws an EvalException
   *  on the first call to next().
   */
  public ListIterator<Expr> listIterator()
  {
    if (lower_ != null)
      return new RangeSetIterator(lower_, upper_, BigInteger.ONE);
    else
      return new RangeSetIterator(upper_, lower_, BigInteger.valueOf(-1));
  }

  @Override
  public Iterator<Expr> sortedIterator()
  {
    if (lower_ == null)
      throw new EvalException("No minimum value for sorted iteration through "
          + " RangeSet " + name_);
    return iterator();
  }

  @Override
  public Iterator<Expr> subsetIterator(EvalSet otherSet)
  {
    if (otherSet instanceof RangeSet)
      return intersect( (RangeSet)otherSet ).iterator();
    else
      return super.subsetIterator(otherSet);
  }

  /** @inheritDoc
   *
   *  This uses bounds information about element (if any)
   *  to reduce the size of the set that is returned.
   *  The set that is returned is guaranteed to be a subset
   *  (or equal to) the true set of elements in the range.
   *  This methods has no side-effects, so does not change the
   *  set returned by the usual members() method.
   */
  /* TODO: this calculates the intersection of two ranges...
  public Iterator<Expr> subsetIterator(ZName element)
  {
    assert bounds_ != null; // inferBounds should have been called.
    Envir env = evalMode_.getEnvir();
    BigInteger low = getBound(env, lowerArg_);
    BigInteger high = getBound(env, upperArg_);
    BigInteger elemLow = bounds_.getLower(element);
    BigInteger elemHigh = bounds_.getUpper(element);

    if (low != null && elemLow != null)
      low = low.max(elemLow);  // take the tighter of the two bounds.
    else if (lowerArg_ < 0)
      low = elemLow; // real lower bound is infinite, so use elemLow.

    if (high != null && elemHigh != null)
      high = high.min(elemHigh);  // take the tighter of the two bounds.
    else if (upperArg_ < 0)
      high = elemHigh; // real upper bound is infinite, so use elemHigh.

    if (low == null || high == null)
      throw new EvalException("Unbounded integer "+element+" in "+this);

    return new RangeSetIterator(low, high);
  }
  */

  @Override
  public BigInteger getLower()
  {
    return lower_;
  }

  @Override
  public BigInteger getUpper()
  {
    return upper_;
  }

  /** This is a ListIterator that iterates from start to end, using
   *  the given increment value (usually +1 or -1).
   *  If end==null, then the iterator will return an infinite
   *  stream of values.  If both are null, then the first call
   *  to next() will throw an exception.
   *  Like all list iterators, the index methods may return incorrect
   *  results if you do more than 2^31 nexts.
   * @author marku
   *
   */
  private class RangeSetIterator implements ListIterator<Expr>
  {
    protected BigInteger start_;  // may be null
    protected BigInteger current_; // null iff start is null
    protected BigInteger incr_; // non-null
    protected BigInteger end_; // may be null

    /** We throw EvalException when we reach this one. */
    protected BigInteger toomany_; // null iff start is null;

    /** start or end (or both) can be null, but incr must be non-null. */
    public RangeSetIterator(BigInteger start, BigInteger end, BigInteger incr)
    {
      start_ = start;
      current_ = start;
      incr_ = incr;
      end_ = end;
      if (start != null)
        toomany_ = start.add(incr.multiply(BigInteger.valueOf(numIterSize_)));
    }
    public boolean hasNext()
    {
      if (current_ == null || end_ == null)
        return true;
      if (incr_.signum() == 1)
        return (current_.compareTo(end_) <= 0);
      else
        return (current_.compareTo(end_) >= 0);
    }
    public Expr next()
    {
      BigInteger temp = current_;
      if ( ! hasNext())
        throw new NoSuchElementException("too many nexts on "+this);
      if (current_ == null)
        throw new EvalException("Cannot start iteration through ALL integers"
            + " in RangeSet " + name_);
      current_ = current_.add(incr_);
      if (end_ == null && current_.equals(toomany_))
        throw new EvalException("Gave up unbounded iteration from "+
            start_+" by "+incr_+" after "+numIterSize_+" results"
            + " in RangeSet " + name_);
      return factory_.createNumExpr(temp);
    }
    public boolean hasPrevious()
    {
      if (current_ == null)
        return false;
      return (start_.compareTo(current_) != 0);
    }
    public int nextIndex()
    {
      if (current_ == null)
        return 0;  // we are in the initial state.
      int nexts = current_.subtract(start_).divide(incr_).intValue();
      assert nexts >= 0;
      return nexts;
    }
    public Expr previous()
    {
      if ( ! hasPrevious())
        throw new NoSuchElementException("too many previous calls on "+this);
      current_ = current_.subtract(incr_);
      return factory_.createNumExpr(current_);
    }
    public int previousIndex()
    {
      return nextIndex() - 1;
    }
    public void remove()
    {
      throw new UnsupportedOperationException(
          "The ListIterator.Remove Operation is not allowed on "+this);
    }
    public void add(Expr o)
    {
      throw new UnsupportedOperationException(
      "The ListIterator.Add operation is not allowed on "+this);
    }
    public void set(Expr o)
    {
      throw new UnsupportedOperationException(
          "The ListIterator.set(_) operation is not allowed on "+this);
    }
  }

  /** This implementation of equals handles two RangeSets efficiently.
   *  In other cases, it uses the equals method from FlatEvalSet.
   *  This equals method is really only meant to be used after
   *  the sets have been evaluated.  It is not clear what it does
   *  or should do before that.
   */
  public boolean equals(Object other) {
    if (other instanceof RangeSet) {
      RangeSet rset = (RangeSet)other;
      /* An alternative equality test, which is less elegant.
      // handle the no-bounds at all case.
      if (lower_ == null && upper_ == null) {
        return rset.lower_ == null && rset.upper_ == null;
      }
      // handle the no lower bound case.
      if (lower_ == null) {
        // we know that upper_ != null;
        return rset.lower_ == null
            && rset.upper_ != null
            && upper_.compareTo(rset.upper_) == 0;
      }
      // handle the no upper bound case.
      if (upper_ == null) {
        // we know that lower_ != null;
        return rset.lower_ != null
            && rset.upper_ == null
            && lower_.compareTo(rset.lower_) == 0;
      }
      // now we know that lower_ != null and upper_ != null
      if (rset.lower_ == null || rset.upper_ == null)
        return false;
      // now we know that rset.lower_ != null and rset.upper_ != null
      // handle the empty range case (lower_ > upper_) specially.
      if (lower_.compareTo(upper_)>0) {
        return rset.lower_.compareTo(rset.upper_) > 0;
      }
      return lower_.equals(rset.lower_)
          && upper_.equals(rset.upper_);
      */
      if ((lower_ == null) != (rset.lower_ == null))
        return false;
      if ((upper_ == null) != (rset.upper_ == null))
        return false;
      // handle the empty range case (lower_ > upper_) specially.
      if (lower_ != null && upper_ != null
          && lower_.compareTo(upper_)>0) {
        return rset.lower_.compareTo(rset.upper_) > 0;
      }
      else
        return (lower_ == null || lower_.equals(rset.lower_))
            && (upper_ == null || upper_.equals(rset.upper_));
    }
    else
      return super.equals(other);
  }


  /** Calculates the minimum of two optional numbers,
   *  with null interpreted as being negative infinity.
   * @param i1  null means negative infinity
   * @param i2  null means negative infinity
   * @return
   */
  public static BigInteger minNeg(BigInteger i1, BigInteger i2)
  {
    if (i1 == null || i2 == null)
      return null;
    else
      return i1.min(i2);
  }

  /** Calculates the minimum of two optional numbers,
   *  with null interpreted as being positive infinity.
   * @param i1  null means positive infinity
   * @param i2  null means positive infinity
   * @return
   */
  public static BigInteger minPos(BigInteger i1, BigInteger i2)
  {
    if (i1 == null)
      return i2;
    else if (i2 == null)
      return i1;
    else
      return i1.min(i2);
  }

  /** Calculates the maximum of two optional numbers,
   *  with null interpreted as being negative infinity.
   * @param i1  null means negative infinity
   * @param i2  null means negative infinity
   * @return
   */
  public static BigInteger maxNeg(BigInteger i1, BigInteger i2)
  {
    if (i1 == null)
      return i2;
    else if (i2 == null)
      return i1;
    else
      return i1.max(i2);
  }

  /** Calculates the maximum of two optional numbers,
   *  with null interpreted as being positive infinity.
   * @param i1  null means positive infinity
   * @param i2  null means positive infinity
   * @return
   */
  public static BigInteger maxPos(BigInteger i1, BigInteger i2)
  {
    if (i1 == null || i2 == null)
      return null;
    else
      return i1.max(i2);
  }

  /** Calculates the 'generous union' of two ranges.
   *  Generous union means that the resulting range will
   *  include all numbers between the minimum of the two
   *  lower bounds and the maximum of the two upper bounds.
   *  For example, the generous union of 0..3 and 10..12 is
   *  0..12, which includes numbers that are not in either set.
   *  So the generous union will always be a superset
   *  of the real union (or equal to it).
   *  If other==null, then this is returned.
   */
  public RangeSet union(RangeSet other)
  {
    if (other==null)
      return this;
    else
      return new RangeSet(minNeg(lower_, other.getLower()),
                          maxPos(upper_, other.getUpper()),
                          name_ + "_u_" + other.name_);
  }

  /** Calculates the 'generous union' of this range with (lo..up).
   *  Note that lo==null means negative infinity
   *  and up=null means positive infinity.
   */
  public RangeSet union(BigInteger lo, BigInteger up)
  {
    return new RangeSet(minNeg(lower_, lo),
                        maxPos(upper_, up),
                        name_ + "_u");
  }

  /** Calculates the exact intersection of two ranges.
   *  If other==null, then this is returned.
   */
  public RangeSet intersect(RangeSet other)
  {
    if (other == null)
      return this;
    else
      return new RangeSet(maxNeg(lower_, other.getLower()),
                          minPos(upper_, other.getUpper()),
                          name_ + "_n_" + other.name_);
  }

  /** Calculates the exact intersection of this range with (lo..up).
   *  Note that lo==null means negative infinity
   *  and up=null means positive infinity.
   */
  public RangeSet intersect(BigInteger lo, BigInteger up)
  {
    return new RangeSet(maxNeg(lower_, lo),
                        minPos(upper_, up),
                        name_ + "_n");
  }

  /** Returns a possibly-null limit as a string. */
  public static String LimitString(BigInteger limit)
  {
    if (limit == null)
      return "_";
    return limit.toString();
  }

  public String toString()
  {
    return LimitString(lower_) + ".." + LimitString(upper_);
  }
}
