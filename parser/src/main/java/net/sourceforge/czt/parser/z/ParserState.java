/*
  Copyright (C) 2003, 2004, 2005 Tim Miller
  Copyright (C) 2007 Petra Malik
  This file is part of the CZT project.

  The CZT project contains free software;
  you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.z;

public class ParserState
{
  /** The type of the previous chain relation e.g. MEM, EQUALS, IP */
  private int previousChain_ = -1;

  public void setPreviousChain(int previousChain)
  {
    previousChain_ = previousChain;
  }

  public boolean isPreviousChain(int value)
  {
    return previousChain_ == value;
  }
}
