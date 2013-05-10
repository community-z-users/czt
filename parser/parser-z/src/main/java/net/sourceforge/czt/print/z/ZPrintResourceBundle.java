/*
  Copyright (C) 2005, 2006 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.util.ListResourceBundle;

public class ZPrintResourceBundle
  extends ListResourceBundle
{
  private static final Object[][] contents_ = computeContents();

  private static Object[][] computeContents()
  {
    Object[][] result = new Object[ZPrintMessage.values().length][2];
    int i = 0;
    for (ZPrintMessage msg : ZPrintMessage.values()) {
      result[i][0] = msg.toString();
      result[i][1] = msg.getMessage();
      i++;
    }
    return result;
  }

  public Object[][] getContents()
  {
    return contents_;
  }
}
