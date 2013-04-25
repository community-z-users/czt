/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the czt project.
 * 
 * The czt project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The czt project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with czt; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.session;

/**
 * Thrown only when the requested command is not known to the section manager
 * 
 * @author Leo Freitas
 */
public class UnknownCommandException extends CommandException {

  /**
	 * 
	 */
	private static final long serialVersionUID = 2196864863195956907L;

public UnknownCommandException(Dialect d)
  {
	super(d);
  }

  public UnknownCommandException(Dialect d, String message)
  {
    super(d, message);
  }

  public UnknownCommandException(Dialect d, String message, Throwable cause)
  {
    super(d, message, cause);
  }

  public UnknownCommandException(Dialect d, Throwable cause)
  {
    super(d, cause);
  }
}
