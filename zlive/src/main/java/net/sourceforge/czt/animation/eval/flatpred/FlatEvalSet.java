/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.animation.eval.EvalSetVisitor;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** FlatEvalSet is a subclass of FlatPred that implements
 *  the EvalSet interface.  It provides default implementations
 *  of several of the Set methods.  It also provides a lazy-evaluation
 *  mechanism that uses the memberList and memberSet data structures
 *  to record which members of the set have already been evaluated
 *  and to remove duplicates.  The contains() and iterator() methods
 *  are implemented on top of this lazy evaluation mechanism, but
 *  subclasses are free to override those methods and avoid the
 *  lazy evaluation mechanism if they can do it more efficiently
 *  (like FlatRangeSet).
 */
public abstract class FlatEvalSet extends FlatPred implements EvalSet
{
  /** True iff all members of the set have been evaluated. */
  protected boolean fullyEvaluated = false;
  //@invariant fullyEvaluated ==> memberList != null;

  /** The list of known members so far.
   *  This is guaranteed to contain no duplicates.
   *  In some implementations of EvalSet, it will be filled
   *  up lazily as the members of the set are requested.
   *  TODO: to save a little space, we could delete memberList, once
   *  fullyEvaluated becomes true and there are no iterators using it.
   */
  protected List<Expr> memberList;

  /** All the known members of the set.
   *  If memberSet and memberList are both non-null,
   *  then they contain exactly the same elements.
   *  If memberSet is non-null, but memberList is null,
   *  then memberSet contains the complete set.
   */
  protected SortedSet<Expr> memberSet;
  //@invariant memberList==null <==> memberSet==null;
  //@invariant memberList!=null ==> memberList.size()==memberSet.size();

  /** There seems to be no reason to need annotations,
   *  but the interface forces us to have a non-null list.
   */
  private ListTerm<Ann> anns_ = new ListTermImpl<Ann>();

  /** Returns the next expression in the set.
   *  This is used during the first evaluation of
   *  the set.  Once this returns null, the set is
   *  fully evaluated and its elements are all stored
   *  in fullSet.
   * @return The next Expr, or null if there are no more.
   */
  protected abstract Expr nextMember();

  /** Evaluates the next member of the set and inserts it into
   *  memberList and memberSet.  Returns true iff it found and
   *  inserted a new member, or false if the set has been
   *  fully evaluated (in which case, fullyEvaluated will have
   *  been set to true as well).
   */
  private /*synchronized*/ boolean insertMember()
  {
    if (memberList == null) {
      assert memberSet == null;
      memberList = new ArrayList<Expr>();
      memberSet = new TreeSet<Expr>(ExprComparator.create());
    }
    while (true) {
      Expr next = nextMember();
      if (next == null) {
        fullyEvaluated = true;
        return false;
      }
      if ( ! memberSet.contains(next)) {
        memberSet.add(next);
        memberList.add(next);
        return true;
      }
    }
  }

  /** This ensures that the set is completely evaluated and
   *  stored in the memberSet data structure.
   */
  protected void evaluateFully()
  {
    while (insertMember())
    {
      // do nothing
    }
    assert fullyEvaluated;
  }

  /** This resets any cached results from previous evaluations.
   *  This should be called by nextEvaluation in each subclass.
   */
  protected void resetResult()
  {
    fullyEvaluated = false;
    memberList = null;
    memberSet = null;
  }

  /** A lazy iterator through memberList.
   *  It calls insertMember() to fill up memberList when necessary.
   */
  private class EvalSetIterator implements ListIterator<Expr>
  {
    /** The entry in memberList that will be returned next. */
    int position;

    public EvalSetIterator()
    {
      position = 0;
    }

    public /*synchronized*/ boolean hasNext()
    {
      return (memberList != null && position < memberList.size())
        || (! fullyEvaluated && insertMember());
    }

    public Expr next()
    {
      assert position < memberList.size();
      Expr result = memberList.get(position);
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
      return memberList.get(position);
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

  /** Iterate through all members of the set.
   *   It guarantees that there will be no duplicates.
   *   Note: this method must only be called AFTER
   *   nextEvaluation(), because all free variables of the
   *   set must be instantiated before we can enumerate the members
   *   of the set.
   *
   * @return an expression iterator.
   */

  public ListIterator<Expr> listIterator()
  {
    return new EvalSetIterator();
  }

  /** Iterate through all members of the set.
   *   It guarantees that there will be no duplicates.
   *   Note: this method must only be called AFTER
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

  /** @inheritDoc
   *  FlatEvalSet provides a default implementation
   *  that iterates through the whole set.
   */
  public Iterator<Expr> subsetIterator(ZName element)
  {
    return iterator();
  }

  /** @inheritDoc
   *   Note: this method must only be called AFTER
   *   nextEvaluation(), because all free variables of the
   *   set must be instantiated before we can enumerate the members
   *   of the set.
   *
   * @return an Expr iterator.
   */
  public Iterator<Expr> sortedIterator()
  {
    if ( ! fullyEvaluated )
      evaluateFully();
    return memberSet.iterator();
  }

  public /*synchronized*/ boolean contains(Object obj)
  {
    if (memberSet != null && memberSet.contains(obj))
      return true;
    else {
      // evaluate the rest of the set
      assert memberList==null || memberList.size()==memberSet.size();
      int done = 0;
      if (memberList != null)
        done = memberList.size();
      while (insertMember()) {
        if (memberList.get(done).equals(obj))
          return true;
        done++;
      }
    }
    return false;
  }

  /** @inheritDoc
   *  FlatEvalSet provides a default implementation
   *  that always returns null.
   */
  public BigInteger getLower()
  {
    return null;
  }

  /** @inheritDoc
   *  FlatEvalSet provides a default implementation
   *  that always returns null.
   */
  public BigInteger getUpper()
  {
    return null;
  }

  /** @inheritDoc
   *  FlatEvalSet provides a default implementation
   *  that always returns null.
   */
  public BigInteger maxSize()
  {
    return null;
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
    if (memberList != null && memberList.size() > 0)
      return true;
    else
      return insertMember();
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

  /** Returns the exact size (cardinality) of the set.
   *  This forces all the members to be evaluated if they
   *  were not already evaluated.
   *  @return Integer.MAX_VALUE if the set is infinite or too large.
   */
  public int size()
  {
    if ( ! fullyEvaluated) {
      // TODO: trap exceptions due to infinite sets and
      //    return Integer.MAX_VALUE instead of looping forever.
      while (insertMember())
      {
        // do nothing
      }
    }
    return memberSet.size();
  }

  /** Returns an array containing all of the elements in this set. */
  public Object[] toArray()
  {
    evaluateFully();
    return memberSet.toArray();
  }

  /** Returns an array containing all of the elements in this set.
   *  The the runtime type of the returned array is that
   *  of the specified array. */
  public <T> T[] toArray(T[] a)
  {
    evaluateFully();
    return memberSet.toArray(a);
  }

  /** Equality of an EvalSet with another EvalSet or Set.
   *  This is implemented using the ExprComparator class.
   *  TODO: Allow finite.equals(infinite) to be calculated as false, etc.
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

  /** {@inheritDoc}
   *  FlatEvalSet provides a default implementation that
   *  calls estSize(evalMode_.getEnvir()).
   */
  public double estSize()
  {
    assert(evalMode_ != null);
    // TODO: should use the ORIGINAL env here, rather than this
    // output env, which may have a few extra vars added.
    return estSize(evalMode_.getEnvir());
  }

  /** {@inheritDoc}
   *  FlatEvalSet provides a default implementation that
   *  just calls estSize(env).
   */
  public double estSubsetSize(Envir env, ZName elem)
  {
    return estSize(env);
  }

  /** {@inheritDoc}
   *  FlatEvalSet provides a default implementation that
   *  resets some internal variables, but always returns null.
   *  This must be overridden (and called) by subclasses.
   */
  public Mode chooseMode( /*@non_null@*/Envir env)
  {
    this.resetResult();
    return null;
  }
  
  /** {@inheritDoc}
   *  FlatEvalSet overrides this so that it also calls resetResult().
   */
  public void startEvaluation()
  {
    super.startEvaluation();
    this.resetResult();
  }

  /** Returns an empty list of children. */
  public Object[] getChildren()
  {
    return new Object[0];
  }

  /** Throws a RuntimeException. */
  public Term create(Object[] args)
  {
    throw new RuntimeException("EvalSet::create not allowed");
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
}
