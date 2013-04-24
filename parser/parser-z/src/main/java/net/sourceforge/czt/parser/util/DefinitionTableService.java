/*
  Copyright (C) 2004, 2005 Petra Malik
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

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Petra Malik
 */
public class DefinitionTableService
  implements Command
{
  SectionInfo sectInfo_;

  public DefinitionTableService()
  {
    sectInfo_ = null;
  }

  /**
   * Creates a new definition table service.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   * @param sectInfo
   */
  public DefinitionTableService(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public Class<?> getInfoType()
  {
    return DefinitionTable.class;
  }

  public Object run(ZSect sect)
    throws CommandException
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(sectInfo_);
    return visitor.run(sect);
  }

  public Object run(ZSect sect, SectionInfo sectInfo)
    throws CommandException
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(sectInfo);
    return visitor.run(sect);
  }

  @Override
  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    DefinitionTableVisitor visitor = new DefinitionTableVisitor(manager);
    Key<ZSect> key = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(key);
    try
    {
      DefinitionTable table = (DefinitionTable) visitor.run(zsect);
      if (table != null)
      {
        // the dependencies will be captured implicitly
        manager.endTransaction(new Key<DefinitionTable>(name, DefinitionTable.class), table);
        return true;
      }
    }
    catch(CztException e)
    {
      throw new CommandException(manager.getDialect(), "Could not calculate definition table as it raised an exception for " + name +
        " with message " + e.getMessage() + (e.getCause() != null ? (" and cause " + e.getCause().getMessage()) : "") + ".", e);
    }    
    return false;
  }
}
