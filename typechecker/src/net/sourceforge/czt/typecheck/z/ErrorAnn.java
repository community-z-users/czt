/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

import net.sourceforge.czt.z.ast.LocAnn;

/**
 * An class for annotating error messages associated with terms.
 */
public class ErrorAnn
{
  /** The position message. */
  protected String position_;

  /** The line number. */
  protected int lineNr_ = -1;

  /** The column number. */
  protected int columnNr_ = -1;

  /** Source information, i.e. file or url name. */
  protected String source_ = null;

  /** Error message. */
  protected String message_;

  public ErrorAnn(String message)
  {
    message_ = message;
  }

  public ErrorAnn(String position, String message)
  {
    position_ = position;
    message_ = message;
  }

  public ErrorAnn(LocAnn locAnn, String message)
  {
    lineNr_ = locAnn.getLine().intValue();
    columnNr_ = locAnn.getCol().intValue();
    source_ = locAnn.getLoc();
    position_ = "\"" + locAnn.getLoc() + "\", " + "line " + locAnn.getLine() + ": ";
    message_ = message;
  }

  public void setPosition(String position)
  {
    position_ = position;
  }

  public String getPosition()
  {
    return position_;
  }

  public void setMessage(String message)
  {
    message_ = message;
  }

  public String getMessage()
  {
    return message_;
  }

  public int getLine()
  {
    return lineNr_;
  }

  public int getColumn()
  {
    return columnNr_;
  }

  public String getSource()
  {
    return source_;
  }

  public String toString()
  {
    String result = new String();
    if (position_ != null) {
      result += position_;
    }
    result += message_;

    return result;
  }
}
