/*
  Copyright (C) 2004, 2005 Petra Malik
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

  public ParseError()
  {
  }

  public ParseError(String message)
  {
    message_ = message;
  }

  public ParseError(String message, Object token)
  {
    this(message);
    token_ = token;
  }

  public ParseError(String message, Object token, LocInfo locInfo)
  {
    this(message, token);
    source_ = locInfo.getSource();
    line_ = locInfo.getLine();
    column_ = locInfo.getColumn();
  }

  public ParseError(int line, int column, String source, String message)
  {
    this(message);
    line_ = line;
    column_ = column;
    source_ = source;
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

  public void setLine(int line)
  {
    line_ = line;
  }

  public int getColumn()
  {
    return column_;
  }

  public void setColumn(int column)
  {
    column_ = column;
  }

  public String getSource()
  {
    return source_;
  }

  public void setSource(String source)
  {
    source_ = source;
  }

  public String getMessage()
  {
    return message_ + " " + token_;
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("Parse error");
    if (source_ != null) result.append(" in \"" + source_ + "\"");
    if (line_ >= 0) result.append(" line " + line_);
    if (column_ >=0) result.append(" column " + column_ + ": ");
    if (message_ != null) result.append(message_);
    if (token_ != null) result.append(" " + token_);
    return result.toString();
  }
}
