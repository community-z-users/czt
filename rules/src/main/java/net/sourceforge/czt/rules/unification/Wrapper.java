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

import net.sourceforge.czt.base.ast.Term;

/**
 * <p>A wrapper for a term.</p>
 *
 * <p>Wrappers are used during unification to simulate certain
 * behaviours of the term it is wrapped around.  For example, the
 * {@link LispWrapper} simulates a lisp style list of terms that
 * represent a list.</p>
 *
 * <p>Unification would probably work without wrappers, they are
 * mainly used to avoid repeated copying, or to make the unification
 * algorithm itself easier.</p>
 *
 * @author Petra Malik
 */
interface Wrapper
  extends Term
{
  Term getContent();
}
