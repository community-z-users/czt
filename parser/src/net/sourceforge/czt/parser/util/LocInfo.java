/*
  Copyright (C) 2005 Petra Malik
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

public class LocInfo
{
  private String source_;
  private int line_;
  private int column_;

  public LocInfo(String source, int line, int column)
  {
    source_ = source;
    line_ = line;
    column_ = column;
  }

  public String getSource()
  {
    return source_;
  }

  public int getLine()
  {
    return line_;
  }

  public Integer getColumn()
  {
    return column_;
  }

  public String toString()
  {
    return "in " + source_ + " line " + line_ + " column " + column_;
  }
}
