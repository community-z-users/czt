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

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Petra Malik
 */
public class DefinitionTableService
  implements SectionInfoService, Command
{
  SectionInfo sectInfo_;

  /**
   * Creates a new definition table service.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   */
  public DefinitionTableService(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public Class getInfoType()
  {
    return DefinitionTable.class;
  }

  public List getRequiredInfoTypes()
  {
    List result = new ArrayList();
    result.add(DefinitionTable.class);
    return result;
  }

  public Object run(ZSect sect)
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(sectInfo_);
    return visitor.run(sect);
  }

  public Object run(ZSect sect, SectionInfo sectInfo)
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(sectInfo);
    return visitor.run(sect);
  }

  public boolean execute(Context context, Map args)
  {
    SectMan sectman = (SectMan) context;
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(sectman);
    Key input = (Key) args.get("input");
    if (input != null) {
      Key key = new Key(input.getName(), ZSect.class);
      ZSect zsect = (ZSect) context.get(key);
      if (zsect != null) {
        DefinitionTable table = (DefinitionTable) visitor.run(zsect);
        if (table != null) {
          Set dep = visitor.getDependencies();
          dep.add(key);
          context.put(new Key(input.getName(), DefinitionTable.class),
                      table, dep);
          return true;
        }
      }
    }
    return false;
  }
}
