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
import net.sourceforge.czt.util.Visitor;
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

  public EvalSet getBaseSet()
  {
    return baseset_;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof PowerSetVisitor) {
      return ((PowerSetVisitor<R>)visitor).visitPowerSet(this);
    }
    return super.accept(visitor);
  }

  public String toString()
  {
    return "Power(" + baseset_.toString() + ")";
  }

  /**
   * An iterator over the elements of a non-empty power set of a given
   * base set.
   */
  protected class PowerSetIterator
    implements Iterator<DiscreteSet>
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

    /**
     * Not supported by this iterator so throws an
     * UnsupportedOperationException when called.
     */
    public void remove()
    {
      throw new UnsupportedOperationException();
    }
  }

  /**
   * <p>An iterator over a list of sets that adds a given expression
   * to each of the element sets before returning.  The original list
   * is not changed by this.</p>
   */
  protected static class AddElementIterator
    implements Iterator<DiscreteSet>
  {
    /** The List of sets to which an element is to be added. */
    private final List<Expr> list_;

    /** The expr to be added. */
    private final Expr expr_;

    /** The current position */
    private int pos_;

    /** The end position */
    private final int end_;;

    /**
     * Creates a new iterator over the given list from start position
     * to end position that adds the given expression to each of the
     * element sets returned.
     *
     * @param expr the expression to be added to each of the sets returned.
     * @param list the list to be iterated over.  It is assumed that
     *             the elements of that list are of type Collection<Expr>.
     * @param start the start position to start iterating from
     * @param end  the list position at which the iteration will stop
     */
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

    /**
     * Returns a DiscreteSet containing the expression given in the
     * constructor and all the elements of the current list element.
     *
     * @throws ClassCastException if the list element at the current
     *         position is not of type @code{Collection<Expr>}.
     */
    @SuppressWarnings("unchecked")
	public DiscreteSet next()
    {
      DiscreteSet result = new DiscreteSet();
      result.addAll(((Collection<Expr>) list_.get(pos_++)));
      result.add(expr_);
      return result;
    }

    /**
     * Not supported by this iterator so throws an
     * UnsupportedOperationException when called.
     */
    public void remove()
    {
      throw new UnsupportedOperationException();
    }
  }
}
