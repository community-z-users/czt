/*
  Copyright (C) 2005, 2007 Petra Malik
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

package net.sourceforge.czt.session;


/**
 * An exception that is thrown when the execution of a Command fails.
 */
public class CommandException
  extends Exception
{

/**
	 * 
	 */
	private static final long serialVersionUID = -6361202018324228212L;

	
  private final Dialect dialect_;

  public CommandException(Dialect dialect)
  {
	  if (dialect == null) throw new NullPointerException();
	  dialect_ = dialect;
  }

  public CommandException(Dialect d, String message)
  {
    super(message);
    if (d== null) throw new NullPointerException();
    dialect_ = d;
  }

  public CommandException(Dialect d, String message, Throwable cause)
  {
    super(message, cause);
    if (d== null) throw new NullPointerException();
    dialect_ = d;
  }

  public CommandException(Dialect d, Throwable cause)
  {
    super(cause);
    if (d== null) throw new NullPointerException();
    dialect_ = d;
  }
  
  public Dialect getDialect()
  {
	  return dialect_;
  }
}
