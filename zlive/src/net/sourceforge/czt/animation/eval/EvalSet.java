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
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Mark Utting
 *
 * This defines the interface to all different kinds of set objects.
 */
public interface EvalSet extends Expr {

  /** A list of all the free variables that this set depends upon.
   * @return The free variables.
   */
  public Set/*<RefName>*/ freeVars();

  /** Estimate the size of the set. */
  //@ requires getEnvir() != null;
  public double estSize();

  /** Iterate through all members of the set.
   *  It guarantees that there will be no duplicates.
   *
   * @return an Iterator object.
   */
  public Iterator members();

  /** Tests for membership of the set.
   * @param e  The fully evaluated expression.
   * @return   true iff e is a member of the set.
   */
  public boolean isMember(Expr e);

  /**Tests for the equality of any two sets.
     Here, the equality is based upon both the sets
     having the same elements, not taking into consideration
     the duplication of elements.
   */
  public boolean equals(Object o);
}
