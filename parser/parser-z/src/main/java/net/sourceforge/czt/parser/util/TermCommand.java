/*
  Copyright (C) 2005, 2006 Petra Malik
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.AbstractCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

public class TermCommand extends AbstractCommand
{

  /**
   * <p>
   * Command to resolve given named resource Source as either a ZSect or Spec.
   * If either ZSect or Spec are cached, then the manager is updated with a
   * Key(Name,Term) for the resolved ZSect or Spec. Otherwise, the command attempts
   * to parse the given named resource first as a ZSect, next as a Spec if first fails.
   * It adds a Key(Name,Term) if either parse is successful.
   * </p>
   * <p>
   * Within CZT, this command is mostly used by various other printing related commands.
   * </p>
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  @Override
  protected boolean doCompute(String name, SectionManager manager) throws CommandException
  {
    // create a new key for the resource for Term
    final Key<Term> newKey = new Key<Term>(name, Term.class);
    Key<ZSect> zSectKey = new Key<ZSect>(name, ZSect.class);
    Key<Spec> specKey = new Key<Spec>(name, Spec.class);
    traceLog("TermCmd-compute = " + name);

    // if name is a cached ZSection, associate the Term key to it and finish.
    if (manager.isCached(zSectKey)) {
      ZSect zs = manager.get(zSectKey);
      manager.endTransaction(newKey, zs);
      return true;
    }
    // if name is a cached Spec, associate the term key to it and finish.
    if (manager.isCached(specKey)) {
      Spec spec = manager.get(specKey);
      manager.endTransaction(newKey, spec);
      return true;
    }

    // otherwise, the manager doesn't know about the resource.
    Term term = null;
    try {

      // try parsing a ZSect: it requires the name to have a known Source Key
      term = manager.get(zSectKey);
    }
    // if there are no known Source keys for name as ZSect, try parsing it as Spec
    catch (CommandException exception) {
      traceLog("TermCmd-Not-ZSect = try as spec");

      // try parsing a Spec: it requires the name to have a known Source key
      term = manager.get(specKey);
      // if it fails, an CommandException will be raise, and we are done (failing).
    }
    assert term != null;

    // if we get here, term must either be a ZSect or Spec; add it to the manager
    //if (term != null) {
    manager.endTransaction(newKey, term);
    return true;
  }
}
