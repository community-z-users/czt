/*
 * ZChar.java
 * Copyright 2003 Mark Utting
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package net.sourceforge.czt.jedit.zcharmap;

/**
 * A Z character/string together with a description.
 *
 * @author Petra Malik
 */
public class ZChar
{
  private String mLabel;

  /**
   * The Z character represented as a string
   * so that Z constructs consisting of several
   * chars can also be represented.
   */
  private String mUnicode;

  /**
   * The LaTeX macro for this character.
   */
  private String mLatex;

  /**
   * A description for that character.
   */
  private String mDescription;

  /**
   * Creates a new Z character with empty description.
   */
  public ZChar(String character)
  {
    mUnicode = mLabel = character;
    mDescription = "";
  }

  /**
   * @throws NullPointerException if <code>description</code> is
   *                              <code>null</code>.
   */
  public ZChar(String character, String description)
  {
    if (description == null) throw new NullPointerException();
    mLabel = mUnicode = character;
    mDescription = description;
  }

  /**
   * @throws NullPointerException if <code>description</code> is
   *                              <code>null</code>.
   */
  public ZChar(String character, String latex, String description)
  {
    if (description == null) throw new NullPointerException();
    mLabel = mUnicode = character;
    mLatex = latex;
    mDescription = description;
  }

  /**
   * @throws NullPointerException if <code>description</code> is
   *                              <code>null</code>.
   */
  public ZChar(String label, String unicode, String latex, String description)
  {
    if (description == null) throw new NullPointerException();
    mLabel = label;
    mUnicode = unicode;
    mLatex = latex;
    mDescription = description;
  }

  public String getLabel()
  {
    return mLabel;
  }

  public String getUnicode()
  {
    return mUnicode;
  }

  public String getDescription()
  {
    return mDescription;
  }

  public String getLatex()
  {
    return mLatex;
  }

  public String getHexString()
  {
    if (mUnicode.length() == 1) {
      return Integer.toHexString(mUnicode.charAt(0));
    }
    return "    ";
  }

  public String toString()
  {
    return getLabel();
  }
}
