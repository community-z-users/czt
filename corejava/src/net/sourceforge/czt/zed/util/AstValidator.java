/*
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.zed.util;

import net.sourceforge.czt.zed.ast.Term;

/**
 * A validator responsible for managing validation of a Z term.
 *
 * @author Petra Malik
 * @czt.todo Think about how to get information about a possible
 *           validation error.
 * @czt.todo Provide Exceptions that can be thrown
 *           in case the validation cannot be performed.
 */
public interface AstValidator
{
  /**
   * Validates an AST starting at <code>term</code>.
   * returns the root term.
   *
   * @param  term the term to begin validation at.
   * @return <code>true</code> if the term is valid,
   *         <code>false</code> otherwise.
   */
  public boolean validate(Term term);
}
