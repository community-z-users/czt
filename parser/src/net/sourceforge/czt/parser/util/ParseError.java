/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

import java.text.MessageFormat;
import java.util.ResourceBundle;

/**
 * A parse error.
 *
 * @author Petra Malik
 */
public abstract class ParseError
  implements CztError
{
  private int line_;
  private int column_;
  private String source_;
  private String message_;
  private Object[] params_;

  public ParseError(String message, Object[] params, LocInfo locInfo)
  {
    message_ = message;
    params_ = params;
    setLocation(locInfo);
  }

  protected abstract String getResourceName();

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

  public void setLocation(LocInfo locInfo)
  {
    if (locInfo == null) return;
    source_ = locInfo.getSource();
    line_ = locInfo.getLine() + 1;
    column_ = locInfo.getColumn() + 1;
  }

  public String getMessage()
  {
    String localized =
      ResourceBundle.getBundle(getResourceName()).getString(message_);
    MessageFormat form = new MessageFormat(localized);
    return form.format(params_);
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    if (source_ != null) result.append("\"" + source_ + "\"");
    if (line_ >= 0) result.append(" line " + line_);
    if (column_ >=0) result.append(" column " + column_ + ": ");
    return result.toString() + getMessage();
  }
}
