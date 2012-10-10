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

import net.sourceforge.czt.parser.util.SectParsableCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * <p>
 * A command to compute the proof table (class ProofTable) of a Z section. Since the ProofTable can be
 * calculated during the ZSect parse, a special handling is required to get correct transaction
 * sequence. The command allows the ProofTable to be calculated during the parse, or via a
 * {@link ProofTableVisitor} otherwise, on a parsed ZSect.
 * </p>
 * <p>
 * Refer to {@link SectParsableCommand} for the algorithm, transaction management and contracts.
 * </p>
 * 
 * @see SectParsableCommand
 * @author Andrius Velykis
 */
public class ProofTableCommand extends SectParsableCommand<ProofTable>
{
  
  @Override
  protected Key<ProofTable> getKey(String name)
  {
    return new Key<ProofTable>(name, ProofTable.class);
  }

  @Override
  protected ProofTable calculateFromSect(ZSect sect, SectionManager manager)
    throws CommandException
  {
    ProofTableVisitor visitor = new ProofTableVisitor(manager);
    return visitor.run(sect);
  }
}
