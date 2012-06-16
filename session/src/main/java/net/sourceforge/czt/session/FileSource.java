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

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * Source from a file.
 */
public class FileSource
  extends Source
{
  private File file_;

  /**
   * @param filename
   * @throws NullPointerException if filename is <code>null</code>.
   */
  public FileSource(String filename)
  {
    this(new File(filename));
  }

  /**
   * @param file
   * @throws NullPointerException if file is <code>null</code>.
   */
  public FileSource(File file)
  {
    if (file == null) throw new NullPointerException();
    file_ = file;
    setName(file_.toString());
    guessSettings(file_.getAbsolutePath());
  }

  @Override
  public String toString()
  {
    return file_.toString();
  }

  @Override
  protected InputStream getStream()
    throws IOException
  {
    return new FileInputStream(file_);
  }
}
