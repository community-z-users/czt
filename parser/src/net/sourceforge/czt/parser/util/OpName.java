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
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;

/**
 * Responsible for transforming opnames to and from strings.
 */
public class OpName
{
  String name_;
  List list_ = new ArrayList();

  public OpName(String name)
    throws OpNameException
  {
    name_ = name;
    String[] split = name.split(ZString.OP_SEPARATOR);
    for (int i = 0; i < split.length; i++) {
      if (split[i] != null && ! split[i].equals("")) {
        list_.add(split[i]);
      }
    }
    if (list_.size() <= 1) {
      throw new OpNameException();
    }
  }

  public String getName()
  {
    return name_;
  }

  /**
   * Returns whether the given string contains an OP_SEPARATOR,
   * i.e. whether the given string is supposed to be an operator name.
   */
  public static boolean isOpName(String name)
  {
    for (int i = 0; i < name.length(); i++) {
      if (ZString.OP_SEPARATOR.equals(String.valueOf(name.charAt(i)))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether this operator is unary,
   * i.e. does contain exactly one ARG or LISTARG.
   *
   * @czt.todo This method can be implemented in a more efficient way.
   */
  public boolean isUnary()
  {
    assert list_.size() >= 2;
    final String ARG = ZString.ARG;
    final String LISTARG = ZString.LISTARG;
    final String first = (String) list_.get(0);
    boolean sizeIsTwo = list_.size() == 2;
    boolean sizeIsThree = list_.size() == 3;
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
  public Iterator iterator()
  {
    return list_.iterator();
  }

  public class OpNameException
    extends Exception
  {
    public OpNameException()
    {
      super();
    }

    public OpNameException(String message)
    {
      super(message);
    }

    public OpNameException(String message, Throwable cause)
    {
      super(message, cause);
    }

    public OpNameException(Throwable cause)
    {
      super(cause);
    }
  }
}
