/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * A class for holding the results of unification. A partial
 * unificiation (PARTIAL), must be created with the types that are not
 * unified.
 */
final public class UResult
{
  /** The possible results of a unification. */
  /** Succeed. */
  public static final UResult SUCC = new UResult("SUCC");

  /** Partial (there are still variable types). */
  public static final UResult PARTIAL = new UResult("PARTIAL");

  /** Failure. */
  public static final UResult FAIL = new UResult("FAIL");

  protected final String name_;

  /**
   * Only this class can create instances.
   */
  private UResult(String name)
  {
    name_ = name;
  }

  public String toString()
  {
    return name_;
  }

  public static UResult conj(UResult left, UResult right)
  {
    UResult result = SUCC;
    if (left == FAIL || right == FAIL) {
      result = FAIL;
    }
    else if (left == PARTIAL || right == PARTIAL) {
      result = PARTIAL;
    }
    return result;
  }
}
