/*
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

public class Pair<X, Y>
{
  private X first_;
  private Y second_;

  public Pair(X first, Y second)
  {
    first_ = first;
    second_ = second;
  }

  public X getFirst()
  {
    return first_;
  }

  public Y getSecond()
  {
    return second_;
  }
}
