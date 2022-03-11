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

import net.sourceforge.czt.z.ast.Expr;

/** A partially-known set.
 *  This records some approximate details about the size and
 *  bounds of another set, but it cannot be used to iterate
 *  through the members of the set etc.
 *  It can be used to record information about sets in Bounds,
 *  but should never be put into an Envir, because there it would
 *  masquerade as the real solution.
 *
 * @author marku
 *
 */
public class FuzzySet extends EvalSet
{
  protected String name_;
  protected double estSize_;
  protected BigInteger maxSize_;
  protected BigInteger lower_;
  protected BigInteger upper_;

  public FuzzySet(String name, double estSize, BigInteger maxSize)
  {
    name_ = name;
    estSize_ = estSize;
    maxSize_ = maxSize;
  }

  @Override
  public BigInteger maxSize()
  {
    return maxSize_;
  }

  public int size()
  {
    throw new FuzzySetException("size called too early on set: "+name_);
  }

  @Override
  public double estSize()
  {
    return estSize_;
  }

  public Iterator<Expr> iterator()
  {
    throw new FuzzySetException("iterator called too early on set: "+name_);
  }

  public ListIterator<Expr> listIterator()
  {
    throw new FuzzySetException("listIterator called too early on set: "+name_);
  }

  @Override
  public java.util.Iterator<Expr> sortedIterator()
  {
    throw new FuzzySetException("sortedIterator called too early on set: "+name_);
  }

  @Override
  public Iterator<Expr> subsetIterator(EvalSet other)
  {
    throw new FuzzySetException("subsetIterator called too early on set: "+name_);
  }

  public boolean contains(Object obj)
  {
    throw new FuzzySetException("contains called too early on set: "+name_);
  }

  @Override
  public boolean containsAll(java.util.Collection<?> c)
  {
    throw new FuzzySetException("containsAll called too early on set: "+name_);
  }

  public boolean isEmpty()
  {
    throw new FuzzySetException("isEmpty called too early on set: "+name_);
  }

  @Override
  public boolean equals(Object s2)
  {
    throw new FuzzySetException("equals called too early on set: "+name_);
  }

  public BigInteger getLower()
  {
    return lower_;
  }

  /** Set the optional lower bound.
   *
   * @param lower  Null means no known lower bound.
   */
  public void setLower(BigInteger lower)
  {
    this.lower_ = lower;
  }

  public BigInteger getUpper()
  {
    return upper_;
  }

  /** Set the optional upper bound.
   *
   * @param upper  Null means no known upper bound.
   */
  public void setUpper(BigInteger upper)
  {
    this.upper_ = upper;
  }

  /** Outputs "set(estSize,maxSize)", or
   *  "set(estSize,maxSize,Range)" if integer bounds information is known.
   */
  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("set(");
    result.append(estSize());
    result.append(",");
    result.append(maxSize_);
    if (lower_ != null || upper_ != null) {
      result.append(",");
      result.append(new RangeSet(lower_, upper_).toString());
    }
    result.append(")");
    return result.toString();
  }
}
