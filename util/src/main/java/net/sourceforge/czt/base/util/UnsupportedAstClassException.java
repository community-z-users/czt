/*
  Copyright (C) 2005, 2007 Mark Utting
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

package net.sourceforge.czt.base.util;

/**
 * An exception thrown by visitors when an unexpected AST class has
 * been found.
 */
public class UnsupportedAstClassException
  extends net.sourceforge.czt.util.CztException
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 6247636028827356285L;

public UnsupportedAstClassException()
  {
  }

  public UnsupportedAstClassException(String message)
  {
    super(message);
  }

  public UnsupportedAstClassException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public UnsupportedAstClassException(Throwable cause)
  {
    super(cause);
  }
}
