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

package net.sourceforge.czt.session;

import java.io.InputStream;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;

public class StringSource
  extends Source
{
  private String string_;

  /**
   * @throws NullPointerException if value is <code>null</code>.
   */
  public StringSource(String value)
  {
    if (value == null) throw new NullPointerException();
    string_ = value;
  }

  public String toString()
  {
    return "StringSource";
  }

  protected InputStream getStream()
    throws IOException
  {
    throw new UnsupportedOperationException();
  }

  public Reader getReader()
    throws IOException
  {
    return new StringReader(string_);
  }
}
