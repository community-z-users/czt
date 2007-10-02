/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.parser.zpatt;

import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

/**
 * An enumeration of Z Patter tokens.
 */
public enum JokerToken
  implements Token
{
  JOKERNAME,
  JOKERNAMELIST,
  JOKERRENAMELIST,
  JOKEREXPR,
  JOKEREXPRLIST,
  JOKERPRED,
  JOKERDECLLIST,
  JOKERSTROKE;

  private JokerToken()
  {
  }

  public String getName()
  {
    return toString();
  }

  public Object getSpelling()
  {
    return null;
  }

  public String spelling()
  {
    return null;
  }

  public NewlineCategory getNewlineCategory()
  {
    return NewlineCategory.NEITHER;
  }
}
