/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.parser.z;

import net.sourceforge.czt.parser.util.Token;

public class ZToken
  implements Token
{
  private TokenName name_;
  private Object spelling_;

  public ZToken(TokenName name)
  {
    name_ = name;
  }

  public ZToken(TokenName name, Object spelling)
  {
    name_ = name;
    spelling_ = spelling;
  }

  public String getName()
  {
    return name_.toString();
  }

  public TokenName getTokenName()
  {
    return name_;
  }

  public Object getSpelling()
  {
    return spelling_;
  }

  public int getLine()
  {
    return -1;
  }

  public int getColumn()
  {
    return -1;
  }

  public int getRightCharPosition()
  {
    return -1;
  }

  public int getLeftCharPosition()
  {
    return -1;
  }

  public String toString()
  {
    return spelling_ != null ? spelling_.toString() : name_.spelling();
  }
}
