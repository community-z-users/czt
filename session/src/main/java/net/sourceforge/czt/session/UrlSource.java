/*
  Copyright (C) 2005, 2007 Petra Malik
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

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

/**
 * A source from an URL.
 */
public class UrlSource
  extends Source
{
  /**
   * The URL (must not be null).
   */
  private URL url_;

  /**
   * @throws NullPointerException if url is <code>null</code>.
   */
  public UrlSource(URL url)
  {
    if (url == null) throw new NullPointerException();
    url_ = url;
    setName(url_.toString());
    guessSettings(url.toString());
  }

  public String toString()
  {
    return url_.toString();
  }

  protected InputStream getStream()
    throws IOException
  {
    return url_.openStream();
  }
}
