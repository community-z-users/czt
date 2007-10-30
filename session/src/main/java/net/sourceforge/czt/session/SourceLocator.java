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
      manager.put(new Key(name, Source.class), new UrlSource(url));
      return true;
    }
    for (int i = 0; i < suffix_.length; i++) {
      File file = new File(name + suffix_[i]);
      if (file.exists() && ! file.isDirectory()) {
        manager.put(new Key(name, Source.class), new FileSource(file));
        return true;
      }
    }
    String path = (String) manager.getProperty("czt.path");
    for (int i = 0; i < suffix_.length; i++) {
      String filename = path + "/" + name + suffix_[i];
      File file = new File(filename);
      if (file.exists()) {
        manager.put(new Key(name, Source.class), new FileSource(file));
        return true;
      }
    }
    throw new SourceLocatorException(name);
  }

  /**
   * Exception thrown when source could not be found.
   */
  public static class SourceLocatorException
    extends CommandException
  {
    private String name_;

    public SourceLocatorException(String name)
    {
      super("Cannot find source location for section " + name);
      name_ = name;
    }

    public String getName()
    {
      return name_;
    }
  }
}
