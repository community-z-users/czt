/**
Copyright 2003 Tim Miller
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
 * Thrown when a tool cannot find the file containing a parent.
 *
 * @author Tim Miller
 */
public class ParentNotFoundException
  extends RuntimeException
{
  //the parent that cannot be found
  private String parent_ = null;

  /**
   * Constructs a new <code>ParentNotFoundException</code> with the
   * specified parent.
   */
  public ParentNotFoundException(String parent)
  {
    parent_ = parent;
  }

  /**
   * Constructs a new <code>ParentNotFoundException</code> with the
   * specified parent and message.
   */
  public ParentNotFoundException(String parent, String message)
  {
    super(message);
    parent_ = parent;
  }

  public String toString()
  {
    String result = "Cannot find parent " + parent_ + "\n";
    result += super.toString();
    return result;
  }
}
