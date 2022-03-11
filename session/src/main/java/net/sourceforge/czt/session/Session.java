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

/**
 * A session contains a section manager and records the name of the
 * current section.
 */
public class Session
{
  private final SectionManager manager_;
  private String section_ = "";

  public Session(Dialect dialect)
  {
	  section_ = ""; // TODO: shouldn't is be ANONYMNOUS?
	  manager_ = new SectionManager(dialect);
  }
  
  public <T> T get(Class<T> c)
    throws CommandException
  {
    return manager_.get(new Key<T>(section_, c));
  }

  public <T> T get(String section, Class<T> c)
    throws CommandException
  {
    return manager_.get(new Key<T>(section, c));
  }

  public SectionManager getManager()
  {
    return manager_;
  }

  public String getSection()
  {
    return section_;
  }

  public void setSection(String s)
  {
    section_ = s;
  }

  public void setPath(String path)
  {
    if (path == null)
    {
      throw new IllegalArgumentException("Null path is not allowed");
    }
    manager_.setProperty("czt.path", path);
  }

  public void putCommands(Dialect extension)
  {
    manager_.putCommands(extension);
  }
}
