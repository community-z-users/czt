/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2005 Mark Utting

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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import net.sourceforge.czt.z.ast.ZName;

/** Maintains lower and upper bounds for integer variables.
 *  This is a helper class for the range-inference pass of
 *  ZLive, which deduces lower and upper bounds for integer
 *  variables, based on the semantics of each FlatPred operator.
 *  It also stores information about variables that will bind
 *  to sets, since this can help when deducing bounds of the
 *  elements of those sets.  Finally, it records some alias names for
 *  structures such as tuples and bindings.  For example, from an equality
 *  like t=(a,c,d), we record the facts: t.1=a, t.2=c, t.3=d.
 *  
 *  Bounds information is usually attached
 *  to ZName objects, but other objects that represent parts of
 *  a tuple (x.1) or binding (x.k) can also be used, provided they
 *  are immutable and have sensible equals and hashCode methods.
 *  <p>
 *  It records information about whether new bounds information
 *  has recently (since the last call to startAnalysis)
 *  been added.  The implementation may even record <em>which</em>
 *  variables have recently changed, so that clients can decide
 *  whether or not it is worth re-analyzing a given FlatPred.
 *  </p>
 *  <p>
 *  The enterLocalBounds method can be used to clone a Bounds
 *  object, so that local bounds information can be added to it
 *  without affecting the bounds information in the parent.
 *  This class also counts the number of bounds deductions that
 *  it has detected (see the getDeductions method).  Child Bounds
 *  objects typically add their deduction count to their parent,
 *  so that the count at the root of the Bounds tree gives the
 *  total number of deductions that have been made in the current
 *  pass.  The general idea is to continue making passes until no
 *  further deductions are made in a pass, which shows that a fix-point
 *  has been reached.
 *  </p>
 *
 * @author marku
 */
public class Bounds
{
  private static final Logger LOG
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  protected Bounds parent_;
  
  /** The number of bounds deductions in this scope (and child scopes). */
  protected int deductions_ = 0;

  private HashMap<Object, BigInteger> lowerBound_;
  private HashMap<Object, BigInteger> upperBound_;
  private HashMap<Object, EvalSet> set_;
  private Set<Object> changed_;

  /** Create a fresh Bounds object with no bounds values.
   *  @param parent Optional parent to inherit bounds from.
   */
  public Bounds(Bounds parent)
  {
    lowerBound_ = new HashMap<Object, BigInteger>();
    upperBound_ = new HashMap<Object, BigInteger>();
    set_        = new HashMap<Object, EvalSet>();
    changed_    = new HashSet<Object>();
    parent_     = parent;
  }

  /**
   * This is similar to startAnalysis with no parameters, but
   * it also updates the local bounds information from the parent.
   * More precisely, it compares the new parent bounds with the
   * current bounds of this object, adds any new information and
   * remembers which variables have changed.  Then it resets the
   * deduction count to zero.  The same parent must be passed as
   * a parameter each time this method is called, and it must be
   * the same as the parent passed to the constructor.
   * <p>
   * This method should be used in preference to startAnalysis()
   * whenever bounds inference starts on a Bounds object
   * that is within a nested scope, such as a quantifiers or disjunction.
   * The idea is that bounds information from the parent should
   * flow down into the child, but not in the reverse direction
   * (though a few inferBounds methods like in FlatOr may choose to
   * propagate some common bounds information back up to the parent).
   * </p>
   *
   * @param parent  Bounds information from an outer scope.
   */
  public void startAnalysis(Bounds parent)
  {
    assert parent_ == parent;
    changed_.clear();
    // copy bounds from parent to result (the child).
    for (Object key : parent.getLowerKeys())
      addLower(key, parent.getLower(key));
    for (Object key : parent.getUpperKeys())
      addUpper(key, parent.getUpper(key));
    for (Object key : parent.getEvalSetKeys())
      setEvalSet(key, parent.getEvalSet(key));
    // now clear our deduction counter, but retain information
    // about which vars have just received tighter bounds.
    deductions_ = 0;
  }

  /** Resets the deductions counter and marks all vars as not-yet-changed.
   *  This is usually done at the beginning of each bounds inference pass.
   */
  public void startAnalysis()
  {
    changed_.clear();
    deductions_ = 0;
  }

  /** This should be called at the end of each bounds inference pass.
   *  It propagates the deduction count up to the parent (if any).
   *  Note that startAnalysis/endAnalysis calls should always
   *  occur in pairs and should be properly nested.  That is, the
   *  startAnalysis/endAnalysis calls of any child Bounds objects
   *  should all occur in between the startAnalysis and endAnalysis
   *  calls of their parent.
   */
  public void endAnalysis()
  {
    if (parent_ != null)
      parent_.addDeductions(deductions_);
  }

  /** The number of bounds deductions in this scope (and child scopes). */
  public int getDeductions()
  {
    return deductions_;
  }

  /** Increment the deductions counter by count.
   *  This is typically used to tell a parent how many deductions
   *  a child Bounds object has just made.
   */
  public void addDeductions(int count)
  {
    deductions_ += count;
  }

  /** True iff some tighter bounds information has been
   *  deduced (or inherited from a parent) in this inference pass.
   * @return true if new/tighter bounds are available.
   */
  public boolean boundsChanged()
  {
    return changed_.size() > 0;
  }

  /** True iff the bounds of key have changed in this pass. */
  public boolean boundsChanged(Object key)
  {
    return changed_.contains(key);
  }

  /** True iff the bounds of any name in vars have changed. */
  public boolean anyBoundsChanged(Collection<ZName> vars)
  {
    for (ZName name : vars)
      if (boundsChanged(name))
        return true;
    return false;
  }

  /** Returns the keys that have lower bounds. */
  public Set<Object> getLowerKeys()
  {
    return lowerBound_.keySet();
  }

  /** Returns the keys that have upper bounds. */
  public Set<Object> getUpperKeys()
  {
    return upperBound_.keySet();
  }

  /** Returns the keys that have set information. */
  public Set<Object> getEvalSetKeys()
  {
    return set_.keySet();
  }

  public String toString()
  {
    return "Lows="+lowerBound_.toString()
          +"+Highs="+upperBound_.toString()
          +"+Sets="+set_.keySet().toString();
  }

  /** Get the EvalSet for var, if known.
   *
   * @param var  The name of an integer variable.
   * @return     The EvalSet (null means unknown).
   */
  public EvalSet getEvalSet(Object var)
  {
    return set_.get(var);
  }

  /** Set the EvalSet for var.
   *  This increments the deduction counter if there was 
   *  previously no EvalSet information for key, or if
   *  any of the attributes of the EvalSet have decreased.
   *
   * @param var  The name of an integer variable.
   * @param set  A non-null EvalSet (usually a FuzzySet).
   */
  public boolean setEvalSet(/*@non_null@*/Object var, /*@non_null@*/EvalSet set)
  {
    EvalSet old = set_.get(var);
    set_.put(var,set);
    if (old == null
        || set.estSize() < old.estSize()
        || isBetterLowerBound(set.getLower(), old.getLower())
        || isBetterUpperBound(set.getUpper(), old.getUpper())
        ) {
      deductions_++;
      changed_.add(var);
      return true;
    }
    return false;
  }

  /** True iff lo1 is a better (tighter) lower bound than lo2.
   * @param lo1 Optional new lower bound
   * @param lo2 Optional old lower bound
   * @return    true if lo1 > lo2 or if lo1 is non-null and lo2 is null.
   */
  public static boolean isBetterLowerBound(BigInteger lo1, BigInteger lo2)
  {
    if (lo1 == null)
      return false;
    else if (lo2 == null)
      return true;
    else
      // both are non-null
      return lo1.compareTo(lo2) > 0;  // lo1 is greater
  }

  /** True iff lo1 is a better (tighter) upper bound than lo2.
   * @param lo1 Optional new upper bound
   * @param lo2 Optional old upper bound
   * @return    true if lo1 < lo2 or if lo1 is non-null and lo2 is null.
   */
  public static boolean isBetterUpperBound(BigInteger lo1, BigInteger lo2)
  {
    if (lo1 == null)
      return false;
    else if (lo2 == null)
      return true;
    else
      // both are non-null
      return lo1.compareTo(lo2) < 0;  // lo1 is less
  }

  /** Get the optional lower bound for var.
   *
   * @param var  The name of an integer variable.
   * @return     The lower bound (null means -infinity).
   */
  public BigInteger getLower(Object var)
  {
    return lowerBound_.get(var);
  }

  /** Get the optional upper bound for var.
   *
   * @param var  The name of an integer variable.
   * @return     The upper bound (null means -infinity).
   */
  public BigInteger getUpper(Object var)
  {
    return upperBound_.get(var);
  }

  /** Returns the lower and/or upper bounds of an integer
   *  variable (if known), or null otherwise.
   */
  public RangeSet getRange(Object var)
  {
    BigInteger lo = getLower(var);
    BigInteger hi = getUpper(var);
    if (lo == null && hi == null)
      return null;
    else
      return new RangeSet(lo,hi);
  }

  /** Adds another lower bound for var.
   *  The new lower bound is ignored if it is weaker than any
   *  existing lower bound, otherwise it supercedes the old bound
   *  (and the deduction count is incremented).
   *  That is, new bounds are <em>intersected</em> with the old bounds.
   *
   * @param var   The name of an integer variable.
   * @param lower The lower bound (must be non-null).
   * @return      true iff the bound has changed (ie. is tighter).
   */
  public boolean addLower(Object var, /*@non_null@*/BigInteger lower)
  {
    assert lower != null;
    BigInteger old = lowerBound_.get(var);
    if (old == null || lower.compareTo(old) > 0) {
      lowerBound_.put(var, lower);
      deductions_++;
      changed_.add(var);
      return true;
    }
    else
      return false;
  }

  /** Adds another upper bound for var.
   *  The new upper bound is ignored if it is weaker than any
   *  existing upper bound, otherwise it supercedes the old bound
   *  (and the deduction count is incremented).
   *  That is, new bounds are <em>intersected</em> with the old bounds.
   *
   * @param var   The name of an integer variable.
   * @param upper The upper bound (must be non-null).
   * @return      true iff the bound has changed (ie. is tighter).
   */
  public boolean addUpper(Object var, /*@non_null@*/BigInteger upper)
  {
    assert upper != null;
    BigInteger old = upperBound_.get(var);
    if (old == null || upper.compareTo(old) < 0) {
      upperBound_.put(var, upper);
      deductions_++;
      changed_.add(var);
      return true;
    }
    else
      return false;
  }
}
