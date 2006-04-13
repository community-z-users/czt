/**
Copyright (C) 2004 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval;

import java.util.*;
import java.math.BigInteger;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;

/**
 * @author Mark Utting
 *
 * This defines the interface to all different kinds of set objects.
 */
public interface EvalSet extends Expr, Set<Expr> {

  /** Default estimate for the approximate size of an unknown set. */
  public double UNKNOWN_SIZE = 1000000.0;

  /** Get the default environment that this set is using.
   *  The default environment can be set via FlatPred.setMode.
   * @return default Envir, or null if it is not known yet.
   */
  public Envir getEnvir();

  /** The lower bound on numeric elements, if any, else null. */
  public BigInteger getLower();

  /** The upper bound on numeric elements, if any, else null. */
  public BigInteger getUpper();

  /** The maximum size of the set in the default environment.
   *  @return  Upper bound on the size of the set, or null if not known.
 . */
  public BigInteger maxSize();

  /** Estimate the size of the set in the default environment.
   *  The default environment must have been set (via FlatPred.setMode)
   *  before you can call this.
 . */
  //@ requires getEnvir() != null;
  public double estSize();

  /** Estimate the size of the set in a given environment. */
  public double estSize(Envir env);

  /** Estimate the size of {x:this | x=elem} in a given environment.
   *  This allows the bounds of elem to be used to reduce the size of set. 
   */
  public double estSubsetSize(Envir env, ZRefName elem);
  
  /** Iterate through all members of the set.
   *  It guarantees that there will be no duplicates.
   *
   * @return an Iterator object.
   */
  public Iterator<Expr> iterator();
  
  /** Iterate through all members of this set that might
   *  equal element (which need not be known yet).
   *  The result will contain no duplicates.
   *
   * @return an Iterator object.
   */
  public Iterator<Expr> subsetIterator(ZRefName element);
  
  /** Tests for membership of the set.
   * @param e  The fully evaluated expression.
   * @return   true iff e is a member of the set.
   */
  public boolean contains(Object e);

  /**Tests for the equality of any two sets.
     Here, the equality is based upon both the sets
     having the same elements, not taking into consideration
     the duplication of elements.
   */
  public boolean equals(Object o);
}
