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

import java.io.File;
import java.net.URL;

/**
 * A command to compute the URL for a Z section.
 * 
 * This first looks for /lib/<code>name</code>.tex in the CZT sources,
 * then searches for a variety of file extensions in the directory
 * specified by czt.path.
 */
public class SourceLocator
  implements Command
{
  protected final String [] suffix_ = {
    ".tex", ".zed", ".zed8", ".zed16", ".oz", ".oz8", ".oz16",
    ".circus", ".circus8", ".circus16", ".zedpatt", ".zedpatt8", ".zedpatt16",
    ".zml"};

  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    URL url = getClass().getResource("/lib/" + name + ".tex");
    if (url != null) {
      manager.put(new Key<Source>(name, Source.class), new UrlSource(url));
      return true;
    }
    for (int i = 0; i < suffix_.length; i++) {
      File file = new File(name + suffix_[i]);
      if (file.exists() && ! file.isDirectory()) {
        manager.put(new Key<Source>(name, Source.class), new FileSource(file));
        return true;
      }
    }
    String path = (String) manager.getProperty("czt.path");
    for (int i = 0; i < suffix_.length; i++) {
      String filename = path + "/" + name + suffix_[i];
      File file = new File(filename);
      if (file.exists()) {
        manager.put(new Key<Source>(name, Source.class), new FileSource(file));
        return true;
      }
    }
    throw new SourceLocatorException(name, path);
  }

  /**
   * Exception thrown when source could not be found.
   */
  @SuppressWarnings("serial")
  public static class SourceLocatorException
    extends CommandException
  {
    private String name_;
    private String path_;

    public SourceLocatorException(String name, String path)
    {
      super("Cannot find source for section " + name
          + " with czt.path="+path);
      name_ = name;
      path_ = path;
    }

    public String getName()
    {
      return name_;
    }

    public String getPath()
    {
      return path_;
    }
  }
}
