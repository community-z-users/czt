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

  protected Factory factory_ = new Factory();

  public RangeSet(BigInteger lo, BigInteger up)
  {
    lower_ = lo;
    upper_ = up;
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
  @Override
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

  @Override
  public boolean contains(Object e)
  {
     if ( !(e instanceof NumExpr))
       throw new EvalException("Type error: members of FlatRangeSet must be numbers: " + e);
     BigInteger i = ((NumExpr)e).getValue();
     return (lower_ == null || lower_.compareTo(i) <= 0)
         && (upper_ == null || upper_.compareTo(i) >= 0);
   }

  @Override
  public Iterator<Expr> iterator()
  {
    return listIterator();
  }

  @Override
  public ListIterator<Expr> listIterator()
  {
    if (lower_ == null || upper_ == null)
      throw new EvalException("Unbounded integer range "+this);
    return new RangeSetIterator(lower_, upper_);
  }

  @Override
  public Iterator<Expr> sortedIterator()
  {
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
  protected void evaluateFully()
  {
    // already fully evaluated
  }

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

  @Override
  protected Expr nextMember()
  {
    // if this is called, then we forgot to override the calling method.
    throw new RuntimeException("DiscreteSet.nextMember should never be called");
  }

  /** This is a ListIterator that iterates in sorted order from low upto high.
   *  Like all list iterators, the index methods may return incorrect
   *  results if you do more than 2^31 nexts.
   * @author marku
   *
   */
  private class RangeSetIterator implements ListIterator<Expr>
  {
    protected BigInteger lowest_;
    protected BigInteger current_;
    protected BigInteger highest_;

    public RangeSetIterator(BigInteger low, BigInteger high)
    {
      assert(low != null);
      assert(high != null);
      lowest_ = low;
      current_ = low;
      highest_ = high;
    }
    public boolean hasNext()
    {
      return (current_.compareTo(highest_) <= 0);
    }
    public Expr next()
    {
      BigInteger temp = current_;
      if ( ! hasNext())
        throw new NoSuchElementException("too many nexts on "+this);
      current_ = current_.add(BigInteger.ONE);
      return factory_.createNumExpr(temp);
    }
    public boolean hasPrevious()
    {
      return (lowest_.compareTo(current_) < 0);
    }
    public int nextIndex()
    {
      return current_.subtract(lowest_).intValue();
    }
    public Expr previous()
    {
      if ( ! hasPrevious())
        throw new NoSuchElementException("too many previous calls on "+this);
      current_ = current_.subtract(BigInteger.ONE);
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
                          maxPos(upper_, other.getUpper()));
  }

  /** Calculates the 'generous union' of this range with (lo..up).
   *  Note that lo==null means negative infinity
   *  and up=null means positive infinity.
   */
  public RangeSet union(BigInteger lo, BigInteger up)
  {
    return new RangeSet(minNeg(lower_, lo),
                        maxPos(upper_, up));
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
                          minPos(upper_, other.getUpper()));
  }
  
  /** Calculates the exact intersection of this range with (lo..up).
   *  Note that lo==null means negative infinity
   *  and up=null means positive infinity.
   */
  public RangeSet intersect(BigInteger lo, BigInteger up)
  {
    return new RangeSet(maxNeg(lower_, lo),
                        minPos(upper_, up));
  }
  
  public String toString()
  {
    return "[" + lower_ + "," + upper_ + "]";
  }
}
