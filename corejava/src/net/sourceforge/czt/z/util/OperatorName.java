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

package net.sourceforge.czt.z.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;

/**
 * Responsible for transforming opnames to and from strings.
 */
public class OperatorName
{
  String name_;
  List list_ = new ArrayList();

  public OperatorName(String name)
    throws OperatorNameException
  {
    name_ = name;
    String[] split = name.split(ZString.OP_SEPARATOR);
    for (int i = 0; i < split.length; i++) {
      if (split[i] != null && ! split[i].equals("")) {
        list_.add(split[i]);
      }
    }
    if (list_.size() <= 1) {
      throw new OperatorNameException();
    }
  }

  public String getName()
  {
    return name_;
  }

  /**
   * Returns whether the given string is an operator name.
   * More precisely, this method checks whether the given string
   * contains an OP_SEPARATOR.
   */
  public static boolean isOperatorName(String name)
  {
    for (int i = 0; i < name.length(); i++) {
      if (ZString.OP_SEPARATOR.equals(String.valueOf(name.charAt(i)))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether this operator is unary.
   * More precisely, this method checks whether this operator contains
   * exactly one ARG or LISTARG.
   *
   * @czt.todo This method can be implemented in a more efficient way.
   */
  public boolean isUnary()
  {
    if (list_.size() < 2) {
      final String message =
        "A list of size smaller than two cannot occur in operator names.";
      throw new CztException(message);
    }
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
   * OperatorName(" _ + _ ") is translated into ["_", "+", "_"].
   */
  public Iterator iterator()
  {
    return list_.iterator();
  }

  public class OperatorNameException
    extends Exception
  {
    public OperatorNameException()
    {
      super();
    }

    public OperatorNameException(String message)
    {
      super(message);
    }

    public OperatorNameException(String message, Throwable cause)
    {
      super(message, cause);
    }

    public OperatorNameException(Throwable cause)
    {
      super(cause);
    }
  }
}
