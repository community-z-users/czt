/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.zpatt.util;

import net.sourceforge.czt.zpatt.ast.*;

public interface Deduction
{
  /**
   * The name of this deduction.
   */
  String getName();

  /**
   * Searches for the next solution.
   * isValid can be called to see if a solution has been found.
   */
  void next();

  /**
   * Returns wheather this rule is correctly applied to the conclusion.
   */
  boolean isValid();

  /**
   * Returns the children.
   */
  Sequent[] children();
}
