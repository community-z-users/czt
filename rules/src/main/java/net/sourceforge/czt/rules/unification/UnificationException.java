/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.rules.unification;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.rules.ast.*;

/**
 * Thrown when unification has failed.
 *
 * @author Petra Malik
 */
public class UnificationException
  extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 5603709266560944685L;
private String reason_;
  private Object left_;
  private Object right_;

  public UnificationException(Object left, Object right, String reason)
  {
    reason_ = reason;
    left_ = left;
    right_ = right;
  }

  public UnificationException(Object left, Object right,
                              String reason,
                              Throwable cause)
  {
    super(cause);
    reason_ = reason;
    left_ = left;
    right_ = right;
  }

  public String getMessage()
  {
    if (left_ instanceof Term && right_ instanceof Term) {
      return "Cannot unify " + TermToString.apply((Term) left_) + " and "
        + TermToString.apply((Term) right_) + ": " + reason_
        + "\ncaused by: " + getCause();
    }
    return "Cannot unify " + left_ + " and " + right_ + ": " + reason_
      + "\ncaused by: " + getCause();
  }
}
