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
package net.sourceforge.czt.typecheck.z.util;

/**
 * An exception that is thrown when a Type in a set expr or reference
 * expression is not fully determined.
 */
public class UndeterminedTypeException
  extends net.sourceforge.czt.util.CztException
{

  /**
	 * 
	 */
	private static final long serialVersionUID = 8096239002003351253L;

public UndeterminedTypeException(Throwable cause)
  {
    super(cause);
  }

  public UndeterminedTypeException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public UndeterminedTypeException(String message)
  {
    super(message);
  }

  public UndeterminedTypeException()
  {
  }
  
}
