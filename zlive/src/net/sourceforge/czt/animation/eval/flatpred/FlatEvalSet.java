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

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.EvalSet;
import net.sourceforge.czt.z.ast.Expr;

/** FlatEvalSet is a subclass of FlatPred that implements
 *  the EvalSet interface.  It provides default implementations
 *  of several of the Set methods.
 */
public abstract class FlatEvalSet extends FlatPred implements EvalSet
{
  /** The list of known members so far.
   *  This contains no duplicates.
   *  In some implementations of EvalSet, it will be filled
   *  up lazily as the members of the set are requested.
   */
  protected List<Expr> knownMembers;
  
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
    return false;
  }

  public boolean isEmpty()
  {
    Iterator<Expr> i = iterator();
    return i.hasNext();
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
    return 0; // Integer.MAX_VALUE;  // TODO
  }

  /** Returns an array containing all of the elements in this set. */
  public Object[] toArray()
  {
    int size = size(); // forces full evaluation
    if (size == Integer.MAX_VALUE)
      throw new EvalException("Set too large/infinite "+this);
    return knownMembers.toArray();
  }

  /** Returns an array containing all of the elements in this set.
   *  The the runtime type of the returned array is that 
   *  of the specified array. */
  public <T> T[] toArray(T[] a)
  {
    int size = size(); // forces full evaluation
    if (size == Integer.MAX_VALUE)
      throw new EvalException("Set too large/infinite "+this);
    return knownMembers.toArray(a);
  }
  
  /** Equality of an EvalSet with another EvalSet or Set. */
  public boolean equalsEvalSet(/*@non_null@*/EvalSet s1, Object s2) {
    Set<Expr> elems1 = new HashSet<Expr>(s1);
    Set<Expr> elems2 = null;
    if (s2 instanceof EvalSet) {
      elems2 = new HashSet<Expr>((EvalSet) s2);
    } else {
      return false;
    }
    return elems1.equals(elems2);
  }
}
