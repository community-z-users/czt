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
import net.sourceforge.czt.z.ast.ZSect;



public class OpTableService
  implements Command
{
  SectionInfo sectInfo_;

  /**
   * Creates a new operator table service.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   * @param sectInfo
   */
  public OpTableService(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public Class<?> getInfoType()
  {
    return OpTable.class;
  }

  public OpTable run(ZSect sect)
    throws CommandException
  {
    OpTableVisitor visitor = new OpTableVisitor(sectInfo_);
    return visitor.run(sect);
  }

  public OpTable run(ZSect sect, SectionInfo sectInfo)
    throws CommandException
  {
    OpTableVisitor visitor = new OpTableVisitor(sectInfo);
    return visitor.run(sect);
  }

  @Override
  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    OpTableVisitor visitor = new OpTableVisitor(manager);
    Key<ZSect> key = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(key);
    if (zsect != null) {
      OpTable opTable = visitor.run(zsect);
      if (opTable != null) {
        // the dependencies will be captured implicitly
        manager.endTransaction(new Key<OpTable>(name, OpTable.class), opTable);
        return true;
      }
    }
    return false;
  }
}
