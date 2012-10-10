/*
  Copyright (C) 2006 Petra Malik
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

import java.math.BigInteger;

/**
 * @author Petra Malik
 */
public class LocInt
{
  private BigInteger value_;
  private LocInfo locInfo_;

  public LocInt(String value, LocInfo locInfo)
  {
    value_ = new BigInteger(value);
    locInfo_ = locInfo;
  }

  public LocInt(int value, LocInfo locInfo)
  {
    value_ = BigInteger.valueOf(value);
    locInfo_ = locInfo;
  }

  public LocInt(BigInteger value, LocInfo locInfo)
  {
    value_ = value;
    locInfo_ = locInfo;
  }

  public LocInfo getLocation()
  {
    return locInfo_;
  }

  public BigInteger getValue()
  {
    return value_;
  }

  public int getIntValue()
  {
    return value_.intValue();
  }

  public String toString()
  {
    return value_.toString();
  }
}
