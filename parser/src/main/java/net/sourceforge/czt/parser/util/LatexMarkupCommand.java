/*
  Copyright (C) 2006 Petra Malik
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

import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * <p>
 * A command to compute the latex markup function (class LatexMarkupFunction) of a Z section. Since
 * the LatexMarkupFunction can be calculated during the ZSect parse, a special handling is required
 * to get correct transaction sequence. The command allows the LatexMarkupFunction to be calculated
 * during the parse, or via a {@link LatexMarkupFunctionVisitor} otherwise (e.g. for a Unicode
 * ZSect, or for an already-parsed ZSect), on a parsed ZSect.
 * </p>
 * <p>
 * Refer to {@link SectParsableCommand} for the algorithm, transaction management and contracts.
 * </p>
 * 
 * @see SectParsableCommand
 * @author Andrius Velykis
 */
public class LatexMarkupCommand extends SectParsableCommand<LatexMarkupFunction>
{
  
  @Override
  protected Key<LatexMarkupFunction> getKey(String name)
  {
    return new Key<LatexMarkupFunction>(name, LatexMarkupFunction.class);
  }

  @Override
  protected LatexMarkupFunction calculateFromSect(ZSect sect, SectionManager manager)
    throws CommandException
  {
    LatexMarkupFunctionVisitor visitor = new LatexMarkupFunctionVisitor(manager);
    return visitor.run(sect);
  }
}
