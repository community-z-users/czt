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
import java.lang.StringBuffer;
import net.sourceforge.czt.z.ast.ZRefName;

/** Maintains lower and upper bounds for integer variables.
 *  This is a helper class for the range-inference pass of
 *  ZLive, which deduces lower and upper bounds for integer
 *  variables, based on the semantics of each FlatPred operator.
 *  
 * @author marku
 */
public class Bounds implements Cloneable
{
  private HashMap<ZRefName, BigInteger> lowerBound;
  private HashMap<ZRefName, BigInteger> upperBound;

  /** Create a fresh Bounds object with no bounds values.
   */
  public Bounds()
  {
    lowerBound = new HashMap<ZRefName, BigInteger>();
    upperBound = new HashMap<ZRefName, BigInteger>();
  }
  
  public String toString()
  {
    return "Lows="+lowerBound.toString()
          +"Highs="+upperBound.toString();
  }
  
  /** Creates a copy of all the lower and upper bounds.
   *  This is so that the bounds in the copy can be strengthened
   *  independently of the bounds in the original.
   */
  public Bounds clone()
  {
    try {
      Bounds b = (Bounds) super.clone();
      lowerBound = (HashMap<ZRefName, BigInteger>)lowerBound.clone();
      upperBound = (HashMap<ZRefName, BigInteger>)upperBound.clone();
      return b;
    }
    catch (java.lang.CloneNotSupportedException e) {
      throw new net.sourceforge.czt.util.CztException(e);
    }
  }
  
  /** Get the optional lower bound for var.
   * 
   * @param var  The name of an integer variable.
   * @return     The lower bound (null means -infinity).
   */
  public BigInteger getLower(ZRefName var)
  {
    return lowerBound.get(var);
  }
  
  /** Get the optional upper bound for var.
   * 
   * @param var  The name of an integer variable.
   * @return     The upper bound (null means -infinity).
   */
  public BigInteger getUpper(ZRefName var)
  {
    return upperBound.get(var);
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
  public boolean addLower(ZRefName var, /*@non_null@*/BigInteger lower)
  {
    assert lower != null;
    BigInteger old = lowerBound.get(var);
    if (old == null || lower.compareTo(old) > 0) {
      lowerBound.put(var, lower);
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
  public boolean addUpper(ZRefName var, /*@non_null@*/BigInteger upper)
  {
    assert upper != null;
    BigInteger old = upperBound.get(var);
    if (old == null || upper.compareTo(old) < 0) {
      upperBound.put(var, upper);
      return true;
    }
    else
      return false;
  }
}
