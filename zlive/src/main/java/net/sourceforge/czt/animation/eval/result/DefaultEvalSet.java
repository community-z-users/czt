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
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
 *  TODO: move the caching functionality of this class into several
 *  different iterator-wrappers, one that caches elements, another that
 *  converts an Iterator into a ListIterator, etc.  This class could
 *  then be deleted.
 *
 *  This class provides a lazy-evaluation mechanism that uses the
 *  memberList and memberSet data structures to record which members
 *  of the set have already been evaluated and to remove duplicates.
 *  The contains() and iterator() methods are implemented on top of
 *  this lazy evaluation mechanism.
 */
public abstract class DefaultEvalSet
  extends EvalSet
{
  /** True iff all members of the set have been evaluated. */
  private boolean fullyEvaluated_ = false;
  //@invariant fullyEvaluated_ ==> memberList != null;

  /** The list of known members so far.
   *  This is guaranteed to contain no duplicates.
   *  It will be filled up lazily as the members of the set are requested.
   */
  protected List<Expr> memberList_ = new ArrayList<Expr>();

  /** All the known members of the set.
   *  memberSet_ and memberList_ contain exactly the same elements.
   */
  private SortedSet<Expr> memberSet_ =
    new TreeSet<Expr>(ExprComparator.create());
  //@invariant memberList_.size()==memberSet_.size();

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

  /** Enumerates the members of the set.
   *
   * @return an expression iterator.
   */
  public Iterator<Expr> iterator()
  {
    return new EvalSetIterator();
  }

  public Iterator<Expr> sortedIterator()
  {
    if ( ! fullyEvaluated_ )
      evaluateFully();
    return memberSet_.iterator();
  }

  public ListIterator<Expr> listIterator()
  {
    return new EvalSetIterator();
  }

  public Iterator<Expr> subsetIterator(EvalSet otherSet)
  {
    if (otherSet == null)
      return iterator();
    if (otherSet.estSize() < estSize())
      return new SubsetIterator<Expr>(otherSet.iterator(), this);
    else
      return new SubsetIterator<Expr>(this.iterator(), otherSet);
  }

  /** Tests for membership of the set.
   * @param expr  The fully evaluated expression.
   * @return   true iff the given object is a member of the set.
   */
  public boolean contains(Object expr)
  {
    if (memberSet_.contains(expr)) {
      return true;
    }
    // evaluate the rest of the set
    assert memberList_.size()==memberSet_.size();
    int done = memberList_.size();
    while (insertMember()) {
      if (memberList_.get(done).equals(expr))
        return true;
      done++;
    }
    return false;
  }

  public /*synchronized*/ boolean isEmpty()
  {
    // return size() == 0;   //
    if (memberList_.size() > 0) {
      return false;
    }
    return ! insertMember();
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
   *  in <code>memberSet_</code>.
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
    memberList_ = new ArrayList<Expr>();
    memberSet_ = new TreeSet<Expr>(ExprComparator.create());
  }

  /** Returns an array containing all of the elements in this set. */
  @Override
  public Object[] toArray()
  {
    evaluateFully();
    return memberSet_.toArray();
  }

  /** Returns an array containing all of the elements in this set.
   *  The the runtime type of the returned array is that
   *  of the specified array. */
  @Override
  public <T> T[] toArray(T[] a)
  {
    evaluateFully();
    return memberSet_.toArray(a);
  }

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
      return (position < memberList_.size())
        || (! fullyEvaluated_ && insertMember());
    }

    public Expr next()
    {
      if (! hasNext()) throw new NoSuchElementException();
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
