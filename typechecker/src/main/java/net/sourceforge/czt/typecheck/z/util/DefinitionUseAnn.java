/*
  Copyright (C) 2010 Tim Miller
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
package net.sourceforge.czt.typecheck.z.util;

import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.Ann;

/**
 * An annotation for recording the definitions of references names.
 */
public class DefinitionUseAnn

{
  //the ZName that is the declaration of the name
  protected ZName zName_;

  public DefinitionUseAnn(ZName zName)
  {
    zName_ = zName;
  }

  public ZName getZName()
  {
    return zName_;
  }

  public String toString()
  {
    String result = zName_.getWord();
    net.sourceforge.czt.z.ast.LocAnn locAnn = 
      (net.sourceforge.czt.z.ast.LocAnn) zName_.getAnn(net.sourceforge.czt.z.ast.LocAnn.class);
    if (locAnn != null) {
      result += " (" + locAnn.toString() + ")";
    }
    return result;
  }
}
