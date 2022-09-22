/**
Copyright (C) 2004 Petra Malik
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
 * A latex command for Zed markup
 * together with its rendering information.
 *
 * @author Petra Malik
 */
public class LatexCommand
{
  /**
   * The name of this latex command.
   * This does contain the backslash character if present.
   */
  private String name_;

  /**
   * The unicode sequence represented by this latex command.
   */
  private String unicode_;

  /**
   * When translating latex to unicode, space should be added
   * on the leftern side of the unicode sequence if this member is true.
   * This is the case for Zpostchar, Zinchar, Zpostword, and Zinword.
   */
  private boolean addLeftSpace_;

  /**
   * When translating latex to unicode, space should be added
   * on the rightern side of the unicode sequence if this member is true.
   * This is the case for Zprechar, Zinchar, Zpreword, and Zinword.
   */
  private boolean addRightSpace_;

  /**
   * Creates a new latex command.
   *
   * @param name the name of the latex command
   *             (should contain backslash character if present).
   * @param unicode the corresponding unicode sequence represented.
   * @param addLeftSpace a boolean indicating whether space is added
   *             on the leftern side of the unicode sequence when
   *             transforming latex to unicode.
   * @param addRightSpace a boolean indicating whether space is added
   *             on the rightern side of the unicode sequence when
   *             transforming latex to unicode.
   */
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
   * @return the name of this latex command
   *         (contains the backslash character if present).
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

  /**
   * Returns a string representation of this latex command.
   */
  public String toString()
  {
    return name_ + " -> " + unicode_;
  }
}
