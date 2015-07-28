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

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionInfo;

/**
 * This exception can be thrown by a scanner when unexpected tokens
 * are encountered.
 */
public class ScanException
  extends net.sourceforge.czt.util.CztException
  implements CztError
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -5502310625340895712L;
	private transient final LocInfo locInfo_;
  private final String symbolInfo_;
  private final Dialect dialect_;

  /**
   * Constructs a new exception with the specified detail message
   * and location information.
   */
  public ScanException(Dialect dialect, String message, LocInfo locInfo)
  {
    this(dialect, message, null, locInfo);
  }
  
  public ScanException(Dialect dialect, String message, String symbol_info, LocInfo locInfo)
  {
    super(message);
    if (locInfo == null || dialect == null) throw new NullPointerException();
    locInfo_ = locInfo;
    symbolInfo_ = symbol_info;
    dialect_ = dialect;
  }
  
  @Override
public Dialect getDialect()
  {
	  return dialect_;
  }
  
  public LocInfo getLocation()
  {
    return locInfo_;
  }

  @Override
public int getLine()
  {
    return locInfo_.getLine();
  }

  @Override
public int getColumn()
  {
    return locInfo_.getColumn();
  }

  @Override
public int getStart()
  {
    return locInfo_.getStart();
  }

  @Override
public int getLength()
  {
    return locInfo_.getLength();
  }

  @Override
public String getSource()
  {
    return locInfo_.getSource();
  }

  @Override
public ErrorType getErrorType()
  {
    return ErrorType.ERROR;
  }

  @Override
public String getInfo()
  {
    return null;
  }
  
  public String getSymbolInfo()
  {
    return symbolInfo_;
  }

  @Override
public String toString()
  {
    return locInfo_.toString() + ": " + getMessage();
  }
  
  @Override
  public String getMessage()
  {
	  return "[" + getDialect() + " dialect] " + super.getMessage();
  }

  @Override
  public int compareTo(CztError other)
  {
    return CztErrorImpl.compareCztErrorPositionTypeAndMessage(this, other);
  }
  
  @Override
  public boolean equals(Object obj)
  {
	 return CztErrorImpl.compareCztErrorsEquals(this, obj);
  }
  
  @Override
  public int hashCode()
  {
	  int h = super.hashCode();
	  h += CztErrorImpl.baseHashCodeCztError(this);
	  return h;
  }
  
	@Override
	public boolean hasSectionInfo() {
		return false;
	}
	
	@Override
	public SectionInfo getSectionInfo() {
		return null;
	}

}
