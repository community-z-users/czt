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

package net.sourceforge.czt.parser.util;

/**
 * A latex command for Zed markup together with its rendering information.
 * It corresponds to the %%Zchar and %%Zword commands used within latex markup.
 *
 * @author Petra Malik
 */
public class LatexCommand
{
  /**
   * The name of this latex command (does contain the backslash character).
   */
  private String name_;

  /**
   * The unicode sequence represented by this latex command.
   */
  private String unicode_;
  private boolean addLeftSpace_;
  private boolean addRightSpace_;

  public LatexCommand(String name,
                      String unicode,
                      boolean addLeftSpace,
                      boolean addRightSpace)
  {
    name_ = name;
    unicode_ = unicode;
    addLeftSpace_ = addLeftSpace;
    addRightSpace_ = addRightSpace;
  }

  /**
   * Returns the name of this latex command.
   *
   * @return the name of this latex command (contains the backslash character).
   */
  public String getName()
  {
    return name_;
  }

  /**
   * A boolean indicating whether a space is usually inserted before.
   * This is the case for %%Zinchar, %%Zinword, %%Zpostchar, and
   * %%Zpostword definitions.
   */
  public boolean addLeftSpace()
  {
    return addLeftSpace_;
  }

  /**
   * A boolean indicating whether a space is usually inserted after.
   * This is the case for %%Zinchar, %%Zinword, %%Zprechar, and
   * %%Zpreword definitions.
   */
  public boolean addRightSpace()
  {
    return addRightSpace_;
  }

  /**
   * Returns the unicode sequence represented by this latex command.
   *
   * @return the unicode sequence represented by this latex command.
   */
  public String getUnicode()
  {
    return unicode_;
  }

  public String toString()
  {
    return name_ + " " + unicode_;
  }
}
