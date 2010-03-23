/*
  Copyright (C) 2009 Leo Freitas
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

import java.util.*;

import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;

public class ThmTableService implements Command
{
  SectionInfo sectInfo_;

  /**
   * Creates a new named conjecture table service.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.ThmTable.class</code>.
   */
  public ThmTableService(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public Class getInfoType()
  {
    return ThmTable.class;
  }

  public Object run(ZSect sect)
    throws CommandException
  {
    ThmTableVisitor visitor = new ThmTableVisitor(sectInfo_);
    return visitor.run(sect);
  }

  public Object run(ZSect sect, SectionInfo sectInfo)
    throws CommandException
  {
    ThmTableVisitor visitor = new ThmTableVisitor(sectInfo);
    return visitor.run(sect);
  }

  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    ThmTableVisitor visitor = new ThmTableVisitor(manager);
    Key<ZSect> key = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(key);
    if (zsect != null) {
      ThmTable thmTable = (ThmTable) visitor.run(zsect);
      if (thmTable != null) {
        Set dep = visitor.getDependencies();
        dep.add(key);
        manager.put(new Key<ThmTable>(name, ThmTable.class), thmTable, dep);
        return true;
      }
    }
    return false;
  }
}