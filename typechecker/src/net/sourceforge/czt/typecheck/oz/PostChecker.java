/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined.
 */
public class PostChecker
  extends Checker
{
  protected net.sourceforge.czt.typecheck.z.PostChecker zPostChecker;

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPostChecker =
      new net.sourceforge.czt.typecheck.z.PostChecker(typeChecker);
  }

  public Object visitTerm(Term term)
  {
    return term.accept(zPostChecker);
  }
}
