/**
Copyright 2003 Petra Malik
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

package net.sourceforge.czt.gnast.schema;

/**
 * Exception class used for exceptions that occur during parsing
 * an XML Schema document.
 *
 * @author Petra Malik
 */
public class XSDException extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 6202243312829800156L;

public XSDException()
  {
  }

  public XSDException(String message)
  {
    super(message);
  }

  public XSDException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public XSDException(Throwable cause)
  {
    super(cause);
  }
}
