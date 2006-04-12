/*
  Copyright (C) 2005, 2006 Petra Malik
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
 * @author Petra Malik
 */
public class LocInfoImpl
  implements LocInfo
{
  private String source_;
  private int line_;
  private int column_;
  private int start_;
  private int length_;

  public LocInfoImpl(String source,
                     int line, int column,
                     int start, int length)
  {
    source_ = source;
    line_ = line;
    column_ = column;
    start_ = start;
    length_ = length;
  }

  public LocInfoImpl(String source, int line, int column)
  {
    source_ = source;
    line_ = line;
    column_ = column;
    start_ = -1;
    length_ = -1;
  }

  public LocInfoImpl(LocInfo locInfo)
  {
    source_ = locInfo.getSource();
    line_ = locInfo.getLine();
    column_ = locInfo.getColumn();
    start_ = locInfo.getStart();
    length_ = locInfo.getLength();
  }

  public String getSource()
  {
    return source_;
  }

  public int getLine()
  {
    return line_;
  }

  public int getColumn()
  {
    return column_;
  }

  public int getStart()
  {
    return start_;
  }

  public int getLength()
  {
    return length_;
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    if (source_ != null) result.append("\"" + source_ + "\"");
    if (line_ >= 0) result.append(" line " + line_);
    if (column_ >=0) result.append(" column " + column_);
    return result.toString();
  }
}
