/**
Copyright 2003, 2004 Petra Malik
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

package net.sourceforge.czt.parser.util;

/**
 * This exception can be thrown by a scanner when unexpected tokens
 * are encountered.
 */
public class ScanException
  extends RuntimeException
{
  private int lineNr_;
  private int columnNr_;

  /**
   * Constructs a new exception with the specified detail message.
   */
  public ScanException(String message, int lineNr, int columnNr)
  {
    super(message);
    lineNr_ = lineNr;
    columnNr_ = columnNr;
  }

  public int getLineNumber()
  {
    return lineNr_;
  }

  public int getColumnNumber()
  {
    return columnNr_;
  }
}
