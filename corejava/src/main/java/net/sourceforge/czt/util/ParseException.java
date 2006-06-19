/**
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.util;

/**
 * A parse exception used by all kinds of CZT parsers.
 *
 * @author Petra Malik
 */
public class ParseException
  extends Exception
{
  private String reason_;
  private int line_ = -1;
  private int column_ = -1;
  private String source_ = null;

  /**
   * Constructs a new parse exception with the specified message, source
   * line number and column number.
   */
  public ParseException(String reason,
                        String source,
                        int line,
                        int column)
  {
    reason_ = reason;
    line_ = line;
    column_ = column;
    source_ = source;
  }

  public ParseException(String reason,
                        String source,
                        int line,
                        int column,
                        Exception cause) 
  {
    super(cause);
    reason_ = reason;
    line_ = line;
    column_ = column;
    source_ = source;
  }

  /**
   * Constructs a new parse exception with the specified message,
   * line and column number.
   */
  public ParseException(String reason, int line, int column)
  {
    reason_ = reason;
    line_ = line;
    column_ = column;
  }

  /**
   * Returns the line number of this parse error.
   *
   * @return the line number of this parse error.
   */
  public int getLine()
  {
    return line_;
  }

  /**
   * Sets the line number of this parse error.
   *
   * @param line the new line number.
   */
  public void setLine(int line)
  {
    line_ = line;
  }

  /**
   * Returns the column number of this parse error.
   *
   * @return the column number of this parse error.
   */
  public int getColumn()
  {
    return column_;
  }

  /**
   * Sets the column number of this parse error.
   *
   * @param column the new column number.
   */
  public void setColumn(int column)
  {
    column_ = column;
  }

  /**
   * Returns the source where the parse error occured.
   * This can be file name, a string, etc.
   *
   * @return a string representation of the source.
   */
  public String getSource()
  {
    return source_;
  }

  /**
   * Sets the source for this parse error.
   *
   * @param source the new source.
   */
  public void setSource(String source)
  {
    source_ = source;
  }

  public String getMessage()
  {
    String result = "";
    if (source_ != null) {
      result += "Parse error in " + source_ + ":\n";
    }
    result += reason_;
    if (line_ != -1) {
      result += " at line " + line_;
    }
    if (column_ != -1) {
      result += " column " + column_;
    }
    return result;
  }
}
