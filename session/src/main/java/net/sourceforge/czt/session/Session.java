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
  private SectionManager manager_ = new SectionManager();
  private String section_ = "";

  @SuppressWarnings("unchecked")
  public Object get(Class<?> c)
    throws CommandException
  {
    return manager_.get(new Key(section_, c));
  }

  @SuppressWarnings("unchecked")
  public Object get(String section, Class<?> c)
    throws CommandException
  {
    return manager_.get(new Key(section, c));
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
    manager_.setProperty("czt.path", path);
  }

  public void setExtension(String extension)
  {
    manager_.putCommands(extension);
  }
}
