/*
  Copyright (C) 2004 Petra Malik
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

public class ParseError
{
  private int line_;
  private int column_;
  private String source_;
  private String message_;
  private Object token_;

  public ParseError(int line, int column, String source, String message)
  {
    line_ = line;
    column_ = column;
    source_ = source;
    message_ = message;
  }

  public ParseError(int line, int column,
                    String source, String message,
                    Object token)
  {
    this(line, column, source, message);
    token_ = token;
  }

  public int getLine()
  {
    return line_;
  }

  public int getColumn()
  {
    return column_;
  }

  public String getSource()
  {
    return source_;
  }

  public String getMessage()
  {
    return message_;
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("Parse error in \"" + source_ + "\"");
    result.append(", line " + line_);
    result.append(", column " + column_ + ": ");
    result.append(message_ + " " + token_);
    return result.toString();
  }
}
