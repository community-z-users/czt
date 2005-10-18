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

package net.sourceforge.czt.rules.unification;

import java.util.Set;

import net.sourceforge.czt.zpatt.ast.Binding;

public final class UnificationUtils
{
  /**
   * Do not create instances of this class.
   */
  private UnificationUtils()
  {
  }

  public static Set<Binding> unify(Object o1, Object o2)
  {
    Unifier unifier = new Unifier();
    if (unifier.unify(o1, o2)) return unifier.getBindings();
    for (Binding binding : unifier.getBindings()) {
      binding.reset();
    }
    return null;
  }
}
