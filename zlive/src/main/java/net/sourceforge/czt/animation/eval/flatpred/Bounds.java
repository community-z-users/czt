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
import java.util.HashMap;
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
 *  elements of those sets.
 *  
 *  TODO: add bounds inference for sets of integers.
 *    (we could add upper/lower bounds for s : \power \num,
 *     then the inferBounds methods of the EvalSet subclasses
 *     could propagate the bounds information for those sets.) 
 *  
 * @author marku
 */
public class Bounds implements Cloneable
{
  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  private HashMap<ZName, BigInteger> lowerBound_;
  private HashMap<ZName, BigInteger> upperBound_;
  private HashMap<ZName, EvalSet> set_;

  /** Create a fresh Bounds object with no bounds values.
   */
  public Bounds()
  {
    lowerBound_ = new HashMap<ZName, BigInteger>();
    upperBound_ = new HashMap<ZName, BigInteger>();
    set_        = new HashMap<ZName, EvalSet>();
  }
  
  public String toString()
  {
    return "Lows="+lowerBound_.toString()
          +"+Highs="+upperBound_.toString();
  }
  
  /** Creates a copy of all the lower and upper bounds.
   *  This is so that the bounds in the copy can be strengthened
   *  independently of the bounds in the original.
   */
  public Bounds clone()
  {
    try {
      Bounds b = (Bounds) super.clone();
      lowerBound_ = (HashMap<ZName, BigInteger>)lowerBound_.clone();
      upperBound_ = (HashMap<ZName, BigInteger>)upperBound_.clone();
      set_ = (HashMap<ZName, EvalSet>)set_.clone();
      return b;
    }
    catch (java.lang.CloneNotSupportedException e) {
      throw new net.sourceforge.czt.util.CztException(e);
    }
  }
  
  /** Get the EvalSet for var, if known.
   * 
   * @param var  The name of an integer variable.
   * @return     The EvalSet (null means unknown).
   */
  public EvalSet getEvalSet(ZName var)
  {
    return set_.get(var);
  }
  
  /** Set the EvalSet for var.
   * 
   * @param var  The name of an integer variable.
   * @param set  The EvalSet.
   */
  public boolean setEvalSet(/*@non_null@*/ZName var, /*@non_null@*/EvalSet set)
  {
    EvalSet old = set_.get(var);
    set_.put(var,set);
    return old==null && set!=null;
  }
  
  /** Get the optional lower bound for var.
   * 
   * @param var  The name of an integer variable.
   * @return     The lower bound (null means -infinity).
   */
  public BigInteger getLower(ZName var)
  {
    return lowerBound_.get(var);
  }
  
  /** Get the optional upper bound for var.
   * 
   * @param var  The name of an integer variable.
   * @return     The upper bound (null means -infinity).
   */
  public BigInteger getUpper(ZName var)
  {
    return upperBound_.get(var);
  }

  /** Returns the lower and/or upper bounds of an integer
   *  variable (if known), or null otherwise.
   */
  public RangeSet getRange(ZName var)
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
   *  existing lower bound, otherwise it supercedes the old bound.
   *  That is, new bounds are <em>intersected</em> with the old bounds.
   *  
   * @param var   The name of an integer variable.
   * @param lower The lower bound (must be non-null).
   * @return      true iff the bound has changed (ie. is tighter).
   */
  public boolean addLower(ZName var, /*@non_null@*/BigInteger lower)
  {
    assert lower != null;
    BigInteger old = lowerBound_.get(var);
    if (old == null || lower.compareTo(old) > 0) {
      lowerBound_.put(var, lower);
      sLogger.fine("Bounds lower["+var+"] := "+lower+" instead of "+old);
      return true;
    }
    else
      return false;
  }
  
  /** Adds another upper bound for var.
   *  The new upper bound is ignored if it is weaker than any 
   *  existing upper bound, otherwise it supercedes the old bound.
   *  That is, new bounds are <em>intersected</em> with the old bounds.
   *  
   * @param var   The name of an integer variable.
   * @param upper The upper bound (must be non-null).
   * @return      true iff the bound has changed (ie. is tighter).
   */
  public boolean addUpper(ZName var, /*@non_null@*/BigInteger upper)
  {
    assert upper != null;
    BigInteger old = upperBound_.get(var);
    if (old == null || upper.compareTo(old) < 0) {
      upperBound_.put(var, upper);
      sLogger.fine("Bounds upper["+var+"] := "+upper+" instead of "+old);
      return true;
    }
    else
      return false;
  }

  /**
   * Calculates the minimum of two optional lower bounds.
   * If either of the inputs is null, then the result will
   * also be null, which means negative infinity.
   * 
   * @param lower  null means negative infinity
   * @param lower2 null means negative infinity
   * @return the maximum of lower and lower2
   */
  public static BigInteger lower(BigInteger lower, BigInteger lower2)
  {
    if (lower == null || lower2 == null)
      return null;
    else
      return lower.min(lower2);
  }
}
