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

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * A command to compute the operator table (class OpTable) of a Z section.
 */
public class ThmTableCommand
  implements Command
{
  /**
   * Computes conjectures table for a given ZSection name. It first checks whether
   * there is a ThmTable cached. If there isn't, it retrieves the ZSect for name.
   * This will either parse it or retrieve from the manager (e.g., manually
   * created ZSect). Parsing already updates ThmTable, so it will be cached and found.
   * Finally, for manually added ZSect (e.g., when ThmTable still not cached),
   * it calculates the ThmTable using the visitor.
   *
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  // TODO: why not use the visitor's dependencies as well, like in ThmTableService? (Leo)
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    final Key<ThmTable> key = new Key<ThmTable>(name, ThmTable.class);
    if ( ! manager.isCached(key)) {
      ZSect zSect = manager.get(new Key<ZSect>(name, ZSect.class));
      if ( ! manager.isCached(key)) {
        ThmTableVisitor visitor = new ThmTableVisitor(manager);
        ThmTable thmTable = visitor.run(zSect);
        manager.endTransaction(key, thmTable);
      }
    }
    return true;
  }
}
