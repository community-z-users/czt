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
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
 * @author Mark Utting
 *
 * This defines the interface to all different kinds of ZLive set objects.
 * Note that these set objects may be created in a 'fuzzy' (partially-known)
 * state, where the free variables of the set are not known yet,
 * so the contents of the set are uncertain.  In this state, many of
 * the iterator and size methods may return null or throw an exception.
 *
 * TODO: return more information about each iterator, such as whether or
 * not it is NoDuplicates, Bidirectional, Sorted etc.
 *
 * <p>
 *  EvalSet provides default implementations
 *  of several of the Set methods.
 *  </p>
 */
public abstract class EvalSet
  extends EvalResult
  implements Set<Expr>
{

  /** Default estimate for the approximate size of an unknown set. */
  public static final double UNKNOWN_SIZE = 1000.0;

  /** Default estimate for the approximate size of an infinite set.
   *  We make this slightly less than Double.INFINITY, so that we
   *  can reduce it by halving or taking the log etc.  This allows us
   *  to compare the size of large/'infinite' sets in a simplistic way.
   */
  public static final double INFINITE_SIZE = Double.MAX_VALUE;


  /** There seems to be no reason to need annotations,
   *  but the Expr interface forces us to have a non-null list.
   */
  private ListTerm<Object> anns_ = new ListTermImpl<Object>();

  /** The lower bound on numeric elements, if any, else null.
   *  <p>
   *  FlatEvalSet provides a default implementation
   *  that always returns null.
   *  </p>
   */
  public BigInteger getLower()
  {
    return null;
  }

  /** The upper bound on numeric elements, if any, else null.
   *  <p>
   *  EvalSet provides a default implementation
   *  that always returns null.
   *  </p>
   */
  public BigInteger getUpper()
  {
    return null;
  }

  /** The maximum size of the set in the default environment.
   *  <p>
   *  EvalSet provides a default implementation
   *  that always returns null.
   *  </p>
   *  @return  Upper bound on the size of the set, or null if not known.
   */
  public BigInteger maxSize()
  {
    return null;
  }

  /** Estimate the size of the set.
   *  <p>
   *  EvalSet provides a default implementation that is the same as
   *  maxSize(), but converted to a double.
   *  So maxSize()==null gives EvalSet.INFINITE_SIZE here.
   */
  public double estSize()
  {
    BigInteger size = maxSize();
    if (size == null)
      return EvalSet.INFINITE_SIZE;
    else
      return size.doubleValue();
  }

  /** Estimate the size of {x:this | x=elem} in a given environment.
   *  This allows the bounds of elem to be used to reduce the size of set.
   *  <p>
   *  EvalSet provides a default implementation that
   *  just calls estSize().
   *  </p>
   */
  public double estSubsetSize(Envir env, ZName elem)
  {
    return estSize();
  }

  /** Iterate through all members of the set.
   *  It guarantees that there will be no duplicates.
   *
   * @return an expression iterator.
   */
  public abstract Iterator<Expr> iterator();

  /** Iterate forwards/backwards through all members of the set.
   *  It guarantees that there will be no duplicates.
   *
   * @return a ListIterator object.
   */
  public abstract ListIterator<Expr> listIterator();

  /** Iterate through all members of the set in sorted order.
   *  It guarantees that there will be no duplicates.
   *  It will usually fully evaluate the set before
   *  the first element is returned.  If you want lazy evaluation,
   *  you should use the normal iterator() method instead of this.
   */
  public abstract Iterator<Expr> sortedIterator();

  /** Iterate through the intersection of this set
   *  and the 'other' set.  This is intended purely
   *  to reduce the number of elements visited, so
   *  implementations are free to ignore otherSet if
   *  they wish.  If otherSet==null, then
   *  it places no constraints on the iteration,
   *  and this method is equivalent to iterator().
   *  The result will contain no duplicates.
   *  <p>
   *  EvalSet provides a default implementation
   *  that it iterates through the smaller of the
   *  two sets and checks membership in the other.
   *  TODO: add unit tests for this.
   *  </p>
   * @return an Iterator object.
   */
  public Iterator<Expr> subsetIterator(EvalSet otherSet)
  {
    if (otherSet == null)
      return iterator();
    if (otherSet.estSize() < estSize())
      return new SubsetIterator<Expr>(otherSet.iterator(), this);
    else
      return new SubsetIterator<Expr>(this.iterator(), otherSet);
  }

  /** Iterate through the subset of this set that unifies with
   *  the given substructures in args.  For example, if this set is
   *  a set of triples, then args might map 1 to 42 and 3 to 50,
   *  which would mean that search can be restricted to those triples
   *  that match (42, ?, 50).
   *  <p>
   *  This method is intended purely to reduce the number of elements
   *  visited, so implementations are free to ignore otherSet if
   *  they wish.  The result will contain no duplicates.
   *  <p>
   *  EvalSet provides a default implementation that calls iterator().
   *  </p>
   * @return an Iterator object.
   */
  public Iterator<Expr> matchIterator(Map<Object, Expr> args)
  {
      return iterator();
  }

  public boolean containsAll(Collection<?> c)
  {
    for (Object obj : c)
      if ( ! this.contains(obj))
        return false;
    return true;
  }

  /**Tests for the equality of any two sets.
   * Here, the equality is based upon both the sets
   * having the same elements, not taking into consideration
   * the duplication of elements.
   * This is implemented using the ExprComparator class.
   * TODO: Allow finite.equals(infinite) to be calculated as false, etc.
   */
  public boolean equals(Object s2)
  {
    if (s2 instanceof EvalSet)
      return ExprComparator.create().compare(this, (EvalSet)s2) == 0;
    else
      return false;
  }


  /** This hashCode implementation returns a constant!
   *  The semantics of EvalSet is that its value depends only
   *  upon its members, but we do not want to have to evaluate
   *  all the members before calculating the hashCode, and
   *  it is not very useful (or desirable) to evaluate just
   *  a few members.  So try to avoid creating large
   *  hashsets of EvalSet objects!
   */
  public int hashCode()
  {
    return 13;
  }

  /** Throws UnsupportedOperationException. */
  public boolean add(Expr o)
  {
    throw new UnsupportedOperationException();
  }

  /** Throws UnsupportedOperationException. */
  public boolean addAll(Collection<? extends Expr> c)
  {
    throw new UnsupportedOperationException();
  }

  /** Throws UnsupportedOperationException. */
  public void clear()
  {
    throw new UnsupportedOperationException();
  }

  /** Throws UnsupportedOperationException. */
  public boolean remove(Object o)
  {
    throw new UnsupportedOperationException();
  }

  /** Throws UnsupportedOperationException. */
  public boolean removeAll(Collection<?> c)
  {
    throw new UnsupportedOperationException();
  }

  /** Throws UnsupportedOperationException. */
  public boolean retainAll(Collection<?> c)
  {
    throw new UnsupportedOperationException();
  }

  /** Returns an array containing all of the elements in this set. */
  public Object[] toArray()
  {
    throw new UnsupportedOperationException();
  }

  /** Returns an array containing all of the elements in this set.
   *  The the runtime type of the returned array is that
   *  of the specified array. */
  public <T> T[] toArray(T[] a)
  {
    throw new UnsupportedOperationException();
  }

  /** A copy of the TermImpl implementation. */
  public ListTerm<Object> getAnns()
  {
    return anns_;
  }

  /** A copy of the TermImpl implementation. */
  @SuppressWarnings("unchecked")
public <T> T getAnn(Class<T> aClass)
  {
    for (Object annotation : anns_) {
      if (aClass.isInstance(annotation)) {
        return (T) annotation;
      }
    }
    return null;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof EvalSetVisitor) {
      return ((EvalSetVisitor<R>)visitor).visitEvalSet(this);
    }
    return super.accept(visitor);
  }

  /** Each subclass should implement a nice toString. */
  public abstract String toString();


  /** Filters the master iterator, returning only those
   *  elements that are members of the slave set.
   * @author marku
   */
  public static class SubsetIterator<E> implements Iterator<E>
  {
    private Iterator<E> iter_;
    private EvalSet otherSet_;
    private E nextExpr_;

    public SubsetIterator(Iterator<E> master, EvalSet slave)
    {
      iter_ = master;
      otherSet_ = slave;
      moveToNext();
    }
    private void moveToNext()
    {
      nextExpr_ = null;
      while (nextExpr_ == null && iter_.hasNext()) {
        E e = iter_.next();
        if (otherSet_.contains(e))
          nextExpr_ = e;
      }
    }
    public boolean hasNext()
    {
      return nextExpr_ != null;
    }
    public E next()
    {
      E result = nextExpr_;
      moveToNext();
      return result;
    }
    public void remove()
    {
      throw new UnsupportedOperationException();
    }
  }
}
