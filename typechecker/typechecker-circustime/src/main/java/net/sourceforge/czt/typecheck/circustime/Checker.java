/*
Copyright (C) 2005, 2006, 2007, 2008 Leo Freitas
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
package net.sourceforge.czt.typecheck.circustime;

import net.sourceforge.czt.typecheck.circustime.TypeChecker;

public abstract class Checker<R>
  extends net.sourceforge.czt.typecheck.circus.Checker<R>
{
  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    assert typeChecker != null;
    typeChecker_ = typeChecker;
  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object[] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
      sectName(), GlobalDefs.nearestLocAnn(term), markup());
    return errorAnn;
  }
  
  protected void error(Term term, ErrorMessage errorMsg, Object[] params)
  {
    ErrorAnn errorAnn = errorAnn(term, errorMsg, params);
    error(term, errorAnn);
  }
  }
}

