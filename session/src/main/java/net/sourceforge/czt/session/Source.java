/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.charset.StandardCharsets;

/**
 * The source of a specification.
 * Contains information like endcoding and mark-up.
 */
public abstract class Source
{
  private String encoding_;
  private Markup markup_ = Markup.LATEX;
  private String name_;

  public String getEncoding()
  {
    return encoding_;
  }

  public void setEncoding(String encoding)
  {
    encoding_ = encoding;
  }

  public Markup getMarkup()
  {
    return markup_;
  }

  public void setMarkup(Markup markup)
  {
    markup_ = markup;
  }

  protected abstract InputStream getStream() throws IOException;

  public Reader getReader()
    throws IOException
  {
    final InputStreamReader isr = encoding_ != null ?
      new InputStreamReader(getStream(), encoding_) :
      new InputStreamReader(getStream(), Markup.getDefaultEncoding(markup_));
    return new BufferedReader(isr);
  }

  public String getName()
  {
    return name_;
  }

  public void setName(String name)
  {
    name_ = name;
  }

  /**
   * Tries to guess markup and encoding based on the given string,
   * which is usually the file or url name.
   * @param name
   */
  protected void guessSettings(String name)
  {
    if (name.endsWith(".tex") || name.endsWith(".zed") || name.endsWith("circus")) {
      setMarkup(Markup.LATEX);
    }
    else if (name.endsWith("8")) {
      setMarkup(Markup.UNICODE);
      setEncoding("UTF-8");
    }
    else if (name.endsWith("16")) {
      setMarkup(Markup.UNICODE);
      setEncoding("UTF-16");
    }
    else if (name.endsWith(".xml") || name.endsWith(".zml")) {
      setMarkup(Markup.ZML);
      setEncoding("UTF-8");
    }
  }
}
