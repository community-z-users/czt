/*
  Copyright 2003, 2004, 2007 Petra Malik
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
  implements CztError
{
  private LocInfo locInfo_;
  private String symbolInfo_;

  /**
   * Constructs a new exception with the specified detail message
   * and location information.
   */
  public ScanException(String message, LocInfo locInfo)
  {
    super(message);
    if (locInfo == null) throw new NullPointerException();
    locInfo_ = locInfo;
    symbolInfo_ = null;
  }
  
  public ScanException(String message, String symbol_info, LocInfo locInfo)
  {
    this(message, locInfo);
    symbolInfo_ = symbol_info;
  }
  
  public LocInfo getLocation()
  {
    return locInfo_;
  }

  public int getLine()
  {
    return locInfo_.getLine();
  }

  public int getColumn()
  {
    return locInfo_.getColumn();
  }

  public int getStart()
  {
    return locInfo_.getStart();
  }

  public int getLength()
  {
    return locInfo_.getLength();
  }

  public String getSource()
  {
    return locInfo_.getSource();
  }

  public ErrorType getErrorType()
  {
    return ErrorType.ERROR;
  }

  public String getInfo()
  {
    return null;
  }
  
  public String getSymbolInfo()
  {
    return symbolInfo_;
  }

  public String toString()
  {
    return locInfo_.toString() + ": " + getMessage();
  }

  public int compareTo(CztError other)
  {
    return CztErrorImpl.compareTo(this, other);
  }

}
