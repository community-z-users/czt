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

import java.util.*;
import java.math.BigInteger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
 *  This class provides a lazy-evaluation mechanism that uses the
 *  memberList and memberSet data structures to record which members
 *  of the set have already been evaluated and to remove duplicates.
 *  The contains() and iterator() methods are implemented on top of
 *  this lazy evaluation mechanism, but subclasses are free to
 *  override those methods and avoid the lazy evaluation mechanism if
 *  they can do it more efficiently.
 */
public abstract class DefaultEvalSet
  extends EvalSet
{

  /** Default estimate for the approximate size of an unknown set. */
  public static final double UNKNOWN_SIZE = 1000000.0;

  /** True iff all members of the set have been evaluated. */
  private boolean fullyEvaluated_ = false;
  //@invariant fullyEvaluated_ ==> memberList != null;

  /** The list of known members so far.
   *  This is guaranteed to contain no duplicates.
   *  In some implementations of EvalSet, it will be filled
   *  up lazily as the members of the set are requested.
   *  TODO: to save a little space, we could delete memberList_, once
   *  fullyEvaluated_ becomes true and there are no iterators using it.
   */
  protected List<Expr> memberList_;

  /** All the known members of the set.
   *  If memberSet_ and memberList_ are both non-null,
   *  then they contain exactly the same elements.
   *  If memberSet_ is non-null, but memberList_ is null,
   *  then memberSet_ contains the complete set.
   */
  private SortedSet<Expr> memberSet_;
  //@invariant memberList_==null <==> memberSet_==null;
  //@invariant memberList_!=null ==> memberList_.size()==memberSet_.size();

  /** There seems to be no reason to need annotations,
   *  but the Expr interface forces us to have a non-null list.
   */
  private ListTerm<Ann> anns_ = new ListTermImpl<Ann>();

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
   *  EvalSet provides a default implementation that
   *  returns UNKNOWN_SIZE.
   *  </p>
   */
  public double estSize()
  {
    return UNKNOWN_SIZE;
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

  /** Returns the exact size (cardinality) of the set.
   *  This forces all the members to be evaluated if they
   *  were not already evaluated.
   *  This throws a RuntimeException if it is called when the set is fuzzy.
   *  @return Integer.MAX_VALUE if the set is infinite or too large.
   */
  public int size()
  {
    if ( ! fullyEvaluated_) {
      // TODO: trap exceptions due to infinite sets and
      //    return Integer.MAX_VALUE instead of looping forever.
      while (insertMember())
      {
        // do nothing
      }
    }
    return memberSet_.size();
  }

  /** Iterate through all members of the set.
   *  It guarantees that there will be no duplicates.
   *
   * @return an Iterator object.
   *   Note: this method will return null throw a runtime exception
   *   if it is called must only be called AFTER
   *   nextEvaluation(), because all free variables of the
   *   set must be instantiated before we can enumerate the members
   *   of the set.
   *
   * @return an expression iterator.
   */
  public Iterator<Expr> iterator()
  {
    return new EvalSetIterator();
  }

  /** Iterate through all members of the set in sorted order.
   *  It guarantees that there will be no duplicates.
   *  It will usually fully evaluate the set before
   *  the first element is returned.  If you want lazy evaluation,
   *  you should use the normal iterator() method instead of this.
   */
  public Iterator<Expr> sortedIterator()
  {
    if ( ! fullyEvaluated_ )
      evaluateFully();
    return memberSet_.iterator();
  }

  /** Iterate forwards/backwards through all members of the set.
   *  It guarantees that there will be no duplicates.
   *
   * @return a ListIterator object.
   */
  public ListIterator<Expr> listIterator()
  {
    return new EvalSetIterator();
  }

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
      return new SubsetIterator(otherSet.iterator(), this);
    else
      return new SubsetIterator(this.iterator(), otherSet);
  }
  
  /** Tests for membership of the set.
   * @param e  The fully evaluated expression.
   * @return   true iff e is a member of the set.
   */
  public boolean contains(Object obj)
  {
    if (memberSet_ != null && memberSet_.contains(obj))
      return true;
    else {
      // evaluate the rest of the set
      assert memberList_==null || memberList_.size()==memberSet_.size();
      int done = 0;
      if (memberList_ != null)
        done = memberList_.size();
      while (insertMember()) {
        if (memberList_.get(done).equals(obj))
          return true;
        done++;
      }
    }
    return false;
  }

  public boolean containsAll(Collection<?> c)
  {
    for (Object obj : c)
      if ( ! this.contains(obj))
        return false;
    return true;
  }

  public /*synchronized*/ boolean isEmpty()
  {
    // return size() == 0;   //
    if (memberList_ != null && memberList_.size() > 0)
      return true;
    else
      return insertMember();
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

  /** Returns the next expression in the set.
   *  This is used during the first evaluation of
   *  the set.  Once this returns null, the set is
   *  fully evaluated and its elements are all stored
   *  in fullSet.
   * @return The next Expr, or null if there are no more.
   */
  protected abstract Expr nextMember();

  /** Evaluates the next member of the set and inserts it into
   *  memberList_ and memberSet_.  Returns true iff it found and
   *  inserted a new member, or false if the set has been
   *  fully evaluated (in which case, fullyEvaluated_ will have
   *  been set to true as well).
   */
  private boolean insertMember()
  {
    if (memberList_ == null) {
      assert memberSet_ == null;
      memberList_ = new ArrayList<Expr>();
      memberSet_ = new TreeSet<Expr>(ExprComparator.create());
    }
    while (true) {
      Expr next = nextMember();
      if (next == null) {
        fullyEvaluated_ = true;
        return false;
      }
      if ( ! memberSet_.contains(next)) {
        memberSet_.add(next);
        memberList_.add(next);
        return true;
      }
    }
  }

  /** This ensures that the set is completely evaluated and
   *  stored in the memberSet_ data structure.
   */
  protected void evaluateFully()
  {
    while (insertMember())
    {
      // do nothing
    }
    assert fullyEvaluated_;
  }

  /** This resets any cached results.
   *  TODO: delete this, because the contents of a set should
   *      never change (though they may be enumerated).
   */
  protected void resetResult()
  {
    fullyEvaluated_ = false;
    memberList_ = null;
    memberSet_ = null;
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
    evaluateFully();
    return memberSet_.toArray();
  }

  /** Returns an array containing all of the elements in this set.
   *  The the runtime type of the returned array is that
   *  of the specified array. */
  public <T> T[] toArray(T[] a)
  {
    evaluateFully();
    return memberSet_.toArray(a);
  }

  /** A copy of the TermImpl implementation. */
  public ListTerm<Ann> getAnns()
  {
    return anns_;
  }

  /** A copy of the TermImpl implementation. */
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
    if (visitor instanceof EvalSetVisitor)
      return ((EvalSetVisitor<R>)visitor).visitEvalSet(this);
    else
      return null;
  }
  
  /** Each subclass should implement a nice toString. */
  public abstract String toString();


  /** A lazy iterator through memberList_.
   *  It calls insertMember() to fill up memberList_ when necessary.
   */
  private class EvalSetIterator implements ListIterator<Expr>
  {
    /** The entry in memberList_ that will be returned next. */
    int position;

    public EvalSetIterator()
    {
      position = 0;
    }

    public /*synchronized*/ boolean hasNext()
    {
      return (memberList_ != null && position < memberList_.size())
        || (! fullyEvaluated_ && insertMember());
    }

    public Expr next()
    {
      assert position < memberList_.size();
      Expr result = memberList_.get(position);
      position++;
      return result;
    }

    public void remove()
    {
      throw new UnsupportedOperationException(
          "EvalSet iterators do not support the 'remove' method.");
    }

    public boolean hasPrevious()
    {
      return position > 0;
    }

    public Expr previous()
    {
      assert position > 0;
      position--;
      return memberList_.get(position);
    }

    public int nextIndex()
    {
      return position;
    }

    public int previousIndex()
    {
      return position-1;
    }

    public void set(Expr arg0)
    {
      throw new UnsupportedOperationException(
      "EvalSet iterators do not support the 'set' method.");
    }

    public void add(Expr arg0)
    {
      throw new UnsupportedOperationException(
      "EvalSet iterators do not support the 'add' method.");
    }
  }

  /** Filters the master iterator, returning only those
   *  elements that are members of the slave set.
   * @author marku
   */
  public static class SubsetIterator<Expr> implements Iterator<Expr>
  {
    private Iterator<Expr> iter_;
    private EvalSet otherSet_;
    private Expr nextExpr_;
    
    public SubsetIterator(Iterator<Expr> master, EvalSet slave)
    {
      iter_ = master;
      otherSet_ = slave;
      moveToNext();
    }
    private void moveToNext()
    {
      nextExpr_ = null;
      while (nextExpr_ == null && iter_.hasNext()) {
        Expr e = iter_.next();
        if (otherSet_.contains(e))
          nextExpr_ = e;
      }
    }
    public boolean hasNext()
    {
      return nextExpr_ != null;
    }
    public Expr next()
    {
      Expr result = nextExpr_;
      moveToNext();
      return result;
    }
    public void remove()
    {
      throw new UnsupportedOperationException();
    }
  }
}
