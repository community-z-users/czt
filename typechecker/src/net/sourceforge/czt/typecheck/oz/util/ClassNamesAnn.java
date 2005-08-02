/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz.util;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.z.ast.*;

/**
 * Records the class names declared in an Object-Z specification.
 */
public class ClassNamesAnn
{
  List<DeclName> classNames_;

  public ClassNamesAnn(List<DeclName> classNames)
  {
    classNames_ = list();
    classNames.addAll(classNames);
  }

  public List<DeclName> getClassNames()
  {
    return classNames_;
  }
}
