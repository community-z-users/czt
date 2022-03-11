/*
Copyright 2004 Mark Utting
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
 * This exception indicates that an error has occured
 * while performing a marshal operation.
 *
 * @author Petra Malik
 */
public class MarshalException
  extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 7238845946789102094L;

/**
   * Construct a MarshalException with the specified detail message.
   */
  public MarshalException(String message)
  {
    super(message);
  }

  /**
   * Construct a MarshalException with the specified detail message
   * and cause.
   */
  public MarshalException(String message, Throwable cause)
  {
    super(message, cause);
  }

  /**
   * Construct a MarshalException with the specified cause.
   */
  public MarshalException(Throwable cause)
  {
    super(cause);
  }
}
