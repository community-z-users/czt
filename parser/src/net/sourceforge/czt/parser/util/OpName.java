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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.util.ZString;

/**
 * Responsible for transforming opnames to and from strings.
 */
public class OpName
{
  String name_;

  public OpName(String name)
  {
    name_ = name;
  }

  public String getName()
  {
    return name_;
  }

  /**
   * Checks whether this operator is unary,
   * i.e. does contain exactly one ARG or LISTARG.
   *
   * @czt.todo This method can be implemented in a more efficient way.
   */
  public boolean isUnary()
  {
    List opList = toList();
    assert opList.size() >= 2;
    final String ARG = ZString.ARG;
    final String LISTARG = ZString.LISTARG;
    final String first = (String) opList.get(0);
    boolean sizeIsTwo = opList.size() == 2;
    boolean sizeIsThree = opList.size() == 3;
    boolean firstIsArg = first.equals(ARG) || first.equals(LISTARG);
    return sizeIsTwo || (sizeIsThree && ! firstIsArg);
  }

  public String toString()
  {
    return getName();
  }

  /**
   * OpName(" _ + _ ") is translated into ["_", "+", "_"].
   */
  public List toList()
  {
    List result = new ArrayList();
    String[] split = name_.split(ZString.OP_SEPARATOR);
    for (int i = 0; i < split.length; i++) {
      if (split[i] != null && ! split[i].equals("")) {
        result.add(split[i]);
      }
    }
    return result;
  }
}
