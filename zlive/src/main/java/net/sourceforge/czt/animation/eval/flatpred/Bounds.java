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
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.RangeSet;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
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
 *  <p>
 *  It records information about whether new bounds information
 *  has recently (since the last call to startAnalysis)
 *  been added.  The implementation may even record <em>which</em>
 *  variables have recently changed, so that clients can decide
 *  whether or not it is worth re-analyzing a given FlatPred.
 *  TODO: the record of <em>which</em> variables have changed is not
 *  currently used, and it needs to be updated so that it changes
 *  when aliases are added.
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

  private HashMap<ZName, BigInteger> lowerBound_;
  private HashMap<ZName, BigInteger> upperBound_;
  private HashMap<ZName, EvalSet> set_;
  /** We use a LinkedHashSet so that the first name added (which will always
   *  be a ZName) stays in the same place/order.  We attach all bounds
   *  information for all the aliased names only to this first name.
   */
  private HashMap<ZName, LinkedHashSet<Object>> aliases_;
  private Set<ZName> changed_;

  /** Create a fresh Bounds object with no bounds values.
   *  @param parent Optional parent to inherit bounds from.
   */
  public Bounds(Bounds parent)
  {
    lowerBound_ = new HashMap<ZName, BigInteger>();
    upperBound_ = new HashMap<ZName, BigInteger>();
    set_        = new HashMap<ZName, EvalSet>();
    aliases_    = new HashMap<ZName, LinkedHashSet<Object>>();
    changed_    = new HashSet<ZName>();
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
    for (ZName key : parent.getLowerKeys())
      addLower(key, parent.getLower(key));
    for (ZName key : parent.getUpperKeys())
      addUpper(key, parent.getUpper(key));
    for (ZName key : parent.getEvalSetKeys())
      setEvalSet(key, parent.getEvalSet(key));
    for (ZName key : parent.getAliasKeys())
      for (Object alias : parent.getAliases(key))
        addAlias(key, alias);
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
  public boolean boundsChanged(ZName key)
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
  public Set<ZName> getLowerKeys()
  {
    return lowerBound_.keySet();
  }

  /** Returns the keys that have upper bounds. */
  public Set<ZName> getUpperKeys()
  {
    return upperBound_.keySet();
  }

  /** Returns the keys that have set information. */
  public Set<ZName> getEvalSetKeys()
  {
    return set_.keySet();
  }

  public String toString()
  {
    return "Lows="+lowerBound_.toString()
          +"+Highs="+upperBound_.toString()
          +"+Sets="+set_.keySet().toString()
          +"+Aliases="+aliases_.toString();
  }

  /** Get the EvalSet for var, if known.
   *
   * @param var  The name of an integer variable.
   * @return     The EvalSet (null means unknown).
   */
  public EvalSet getEvalSet(ZName var0)
  {
    ZName var = getBestAlias(var0);
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
  public boolean setEvalSet(/*@non_null@*/ZName var0, /*@non_null@*/EvalSet set)
  {
    ZName var = getBestAlias(var0);
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
  public BigInteger getLower(ZName var)
  {
    return lowerBound_.get(getBestAlias(var));
  }

  /** Get the optional upper bound for var.
   *
   * @param var  The name of an integer variable.
   * @return     The upper bound (null means -infinity).
   */
  public BigInteger getUpper(ZName var)
  {
    return upperBound_.get(getBestAlias(var));
  }

  /** Returns the lower and/or upper bounds of an integer
   *  variable (if known), or null otherwise.
   */
  public RangeSet getRange(ZName var0)
  {
    ZName var = getBestAlias(var0);
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
  public boolean addLower(ZName var0, /*@non_null@*/BigInteger lower)
  {
    ZName var = getBestAlias(var0);
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
  public boolean addUpper(ZName var0, /*@non_null@*/BigInteger upper)
  {
    ZName var = getBestAlias(var0);
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


  /** Returns the keys that have alias information. */
  public Set<ZName> getAliasKeys()
  {
    return aliases_.keySet();
  }

  /** Returns a list of all known aliases for var.
   *  The resulting list will contain ZName, TupleExpr and BindExpr
   *  objects.  For example: getAliases(x) == [ y, z, (a,b,c), (g,h,i') ]
   *  means that x = y = z = (a,b,c) = (g,h,i').
   *
   * @param var
   * @return A list of aliases, which should be treated as read-only.
   */
  public Set<Object> getAliases(ZName var)
  {
    return aliases_.get(var);
  }

  /** Returns the ZName that has the bounds information attached to it.
   *  If var is aliased with other objects, then the bounds information
   *  is always attached to the first object in the LinkedHashSet,
   *  which will always be a ZName.
   */
  protected /*@non_null@*/ZName getBestAlias(/*@non_null@*/ ZName var)
  {
    LinkedHashSet<Object> set = aliases_.get(var);
    if (set == null) {
      return var;
    }
    else {
      return (ZName) set.iterator().next();
    } 
  }

  /** True iff var and other are known to be aliased. */
  public boolean isAliased(ZName var, Object other)
  {
    if (var.equals(other))
      return true;
    Set<Object> known = aliases_.get(var);
    return known != null && known.contains(other);
  }

  /** Add another alias for var.
   *  The alias object must be a ZName,
   *  TupleExpr (which contains only ZName objects),
   *  or BindExpr object (which contains only ZName objects after each ==).
   * @param var
   * @param alias
   */
  public void addAlias(ZName var, Object newAlias)
  {
    if (isAliased(var, newAlias))
      return; // no change needed.
    deductions_++;
    changed_.add(var);
    if (newAlias instanceof ZName) {
      merge(var, (ZName) newAlias);
      // TODO: go through and infer more equalities, from (a,b)=(c,d) etc.
    }
    else {
      assert newAlias instanceof TupleExpr || newAlias instanceof BindExpr;
      Set<Object> known = aliases_.get(var);
      if (known == null) {
        LinkedHashSet<Object> list = new LinkedHashSet<Object>();
        list.add(var);
        list.add(newAlias);
        aliases_.put(var, list);
      }
      else {
        known.add(newAlias);
        // TODO: go through and infer more equalities, from (a,b)=(c,d) etc.
      }
    }
  }

  /** Calculates the union of two alias sets and makes sure that
   * both var1 and var2 point to that union.
   *
   * @param var1
   * @param var2
   * @return Result may be a fresh list, or the one for var1 or var2.
   */
  private void merge(ZName var1, ZName var2)
  {
    LinkedHashSet<Object> list1 = aliases_.get(var1);
    LinkedHashSet<Object> list2 = aliases_.get(var2);
    if (list1 == null && list2 == null) {
      LinkedHashSet<Object> result = new LinkedHashSet<Object>();
      result.add(var1);
      result.add(var2);
      assert result.iterator().next() == var1;
      moveBounds(var2, var1);
      aliases_.put(var1, result);
      aliases_.put(var2, result);
    }
    else if (list1 == null) {
      // list2 is non-null
      assert list2.contains(var2);
      list2.add(var1);
      moveBounds(var1, (ZName) list2.iterator().next());
      aliases_.put(var1, list2);
    }
    else if (list2 == null) {
      // list1 is non-null
      assert list1.contains(var1);
      list1.add(var2);
      moveBounds(var2, (ZName) list1.iterator().next());
      aliases_.put(var2, list1);
    }
    else {
      // both are non-null
      list1.addAll(list2);
      assert list1.contains(var1);
      assert list2.contains(var2);
      moveBounds((ZName) list2.iterator().next(), (ZName) list1.iterator().next());
      aliases_.put(var2, list1);
    }
  }

  /** Moves all bounds information for name 'from' onto name 'to'. */
  private void moveBounds(ZName from, ZName to)
  {
    BigInteger bnd = getLower(from);
    if (bnd != null) {
      addLower(to, bnd);
    }
    bnd = getUpper(from);
    if (bnd != null) {
      addUpper(to, bnd);
    }
    EvalSet set = getEvalSet(from);
    if (set != null) {
      setEvalSet(to, set);
    }
    // TODO: could delete the old bounds
  }
}
