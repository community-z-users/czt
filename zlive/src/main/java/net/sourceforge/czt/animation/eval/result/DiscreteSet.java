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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;

/** A simple implementation of {e1,e2,e3,...,eN}.
 *  A typical usage is to create it, add ALL the members,
 *  then release it to be used in other expressions.
 *  (If other expressions see it before all members are
 *  added, then the size and lower/upper bounds will be wrong).
 *
 * @author marku
 *
 */
public class DiscreteSet extends EvalSet
{
  /** The elements of this set. */
  protected Set<Expr> contents_ = new TreeSet<Expr>(ExprComparator.create());

  /** This is a copy of the elements of this set.
   *  It exists only to allow us to iterate in both directions
   *  (listIterator).  It is created from contents_ automatically
   *  when listIterator() is called and it is an error to try to
   *  add more elements after that point.
   */
  protected List<Expr> listContents_ = null;

  public boolean isEmpty()
  {
    return contents_.isEmpty();
  }

  public int size()
  {
    return contents_.size();
  }

  @Override
  public BigInteger maxSize()
  {
    return BigInteger.valueOf(size());
  }

  @Override
  public double estSize()
  {
    return size();
  }

  public boolean contains(Object obj)
  {
    return contents_.contains(obj);
  }

  @Override
  public Iterator<Expr> iterator()
  {
    // We could return an unmodifiable iterator here...
    return contents_.iterator();
  }

  @Override
  public ListIterator<Expr> listIterator()
  {
    if (listContents_ == null)
      // create a sorted no-duplicates list of elements.
      listContents_ = new ArrayList<Expr>(contents_);
    // We could return an unmodifiable iterator here...
    return listContents_.listIterator();
  }

  @Override
  public Iterator<Expr> sortedIterator()
  {
    return contents_.iterator();
  }

  /** Calculates minimum of all the elements.
   *  Returns null if the set does not contain integers,
   *  or if it is empty.
   */
  @Override
  public BigInteger getLower()
  {
    Iterator<Expr> iter = contents_.iterator();
    if ( ! iter.hasNext())
      return null;
    Expr expr = iter.next();
    if ( ! (expr instanceof NumExpr))
      return null;
    // find the smallest of the integers (they should all be integers)
    NumExpr num = (NumExpr) expr;
    BigInteger result = num.getValue();
    while (iter.hasNext()) {
      num = (NumExpr) iter.next();
      result = result.min(num.getValue());
    }
    return result;
  }

  /** Calculates maximum of all the elements.
   *  Returns null if the set does not contain integers,
   *  or if it is empty.
   *  TODO: return a very negative number if set is empty.
   */
  @Override
  public BigInteger getUpper()
  {
    Iterator<Expr> iter = contents_.iterator();
    if ( ! iter.hasNext())
      return null;
    Expr expr = iter.next();
    if ( ! (expr instanceof NumExpr))
      return null;
    // find the smallest of the integers
    NumExpr num = (NumExpr) expr;
    BigInteger result = num.getValue();
    while (iter.hasNext()) {
      num = (NumExpr) iter.next();
      result = result.max(num.getValue());
    }
    return result;
  }

  @Override
  public boolean add(Expr e)
  {
    if (listContents_ != null)
      throw new RuntimeException("DiscreteSet is closed");
    return contents_.add(e);
  }

  @Override
  public boolean addAll(Collection<? extends Expr> coll)
  {
    boolean changed = false;
    for (Expr e : coll)
      changed |= add(e);
    return changed;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof DiscreteSetVisitor) {
      return ((DiscreteSetVisitor<R>)visitor).visitDiscreteSet(this);
    }
    return super.accept(visitor);
  }

  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("{");
    String sep = "";
    for (Expr e : contents_) {
      result.append(sep);
      result.append(e.toString());
      sep = ", ";
    }
    result.append("}");
    return result.toString();
  }
}
