/*
  Copyright (C) 2006 Petra Malik
  This file is part of the czt project: http://czt.sourceforge.net

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

package net.sourceforge.czt.print.z;

import java.util.ArrayList;

import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.z.util.ZString;

public class DefsWord
  extends Decorword
{
  public DefsWord()
  {
    super(ZString.DEFEQUAL, new ArrayList());
  }
}
