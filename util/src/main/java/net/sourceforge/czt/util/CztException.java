/**
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

package net.sourceforge.czt.util;

/**
 * A runtime exception used for CZT specific errors.
 *
 * @author Petra Malik
 */
public class CztException
  extends RuntimeException
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 8771943245762382460L;

/**
   * Constructs a new CZT exception with <code>null</code> as its message.
   */
  public CztException()
  {
  }

  /**
   * Constructs a new CZT exception with the specified message.
   */
  public CztException(String message)
  {
    super(message);
  }

  /**
   * Constructs a new CZT exception with the specified message
   * and cause.
   */
  public CztException(String message, Throwable cause)
  {
    super(message, cause);
  }

  /**
   * Constructs a new CZT exception with the specified cause.
   * The message is
   * <code>(cause==null ? null : cause.toString())</code>
   * (which typically contains the class and message of cause).
   */
  public CztException(Throwable cause)
  {
    super(cause);
  }
}
