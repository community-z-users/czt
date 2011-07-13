/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.parser.zeves;

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author Leo Freitas
 * @date Jul 13, 2011
 */
public class ProofTableCommand
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
    final Key<ProofTable> key = new Key<ProofTable>(name, ProofTable.class);
    if ( ! manager.isCached(key)) {
      ZSect zSect = manager.get(new Key<ZSect>(name, ZSect.class));
      if ( ! manager.isCached(key)) {
        ProofTableVisitor visitor = new ProofTableVisitor(manager);
        ProofTable proofTable = visitor.run(zSect);
        manager.put(key, proofTable);
      }
    }
    return true;
  }
}
