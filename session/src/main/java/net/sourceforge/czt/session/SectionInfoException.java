/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.session;

import net.sourceforge.czt.util.CztException;

/**
 *
 * @author Leo Freitas
 * @date Feb 2, 2012
 */
public class SectionInfoException extends CztException
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -4019642222369080113L;

/**
   * Constructs a new CZT exception with <code>null</code> as its message.
   */
  public SectionInfoException()
  {
  }

  /**
   * Constructs a new CZT exception with the specified message.
   * @param message 
   */
  public SectionInfoException(String message)
  {
    super(message);
  }

  /**
   * Constructs a new CZT exception with the specified message
   * and cause.
   * @param message
   * @param cause
   */
  public SectionInfoException(String message, Throwable cause)
  {
    super(message, cause);
  }

  /**
   * Constructs a new CZT exception with the specified cause.
   * The message is
   * <code>(cause==null ? null : cause.toString())</code>
   * (which typically contains the class and message of cause).
   * @param cause
   */
  public SectionInfoException(Throwable cause)
  {
    super(cause);
  }
}
