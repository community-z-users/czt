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

import java.util.Collections;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

public class LatexMarkupCommand
  implements Command
{
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    // create keys
    final Key<LatexMarkupFunction> lmfKey = new Key<LatexMarkupFunction>(name, LatexMarkupFunction.class);
    final Key<ZSect> zkey = new Key<ZSect>(name, ZSect.class);

    // if ZSect already parsed, don't cancel LMF transaction
    //    e.x., recall to LMF from outside; call to LMF from a Unicode sect
    // early cancellation would remove the already parsed Unicode ZSect (!)
    if (!manager.isCached(zkey))
    {
      // cancel it only if managed to get lmf key? Trouble is if the source doesn't need LMF (e.g., is Unicode)
      manager.cancelTransaction(lmfKey);
    }

    if (!manager.isCached(lmfKey))
    {
      ZSect zSect = manager.get(zkey);
      if (!manager.isCached(lmfKey))
      {
        // ensure transaction rather than start - we might not cancel it
        // in the case of an already cached ZSect (e.g., unicode one; or user given; etc)
        manager.ensureTransaction(lmfKey);
        
        LatexMarkupFunctionVisitor visitor = new LatexMarkupFunctionVisitor(manager);
        LatexMarkupFunction markup = visitor.run(zSect); 
        manager.endTransaction(lmfKey, markup, Collections.singleton(zkey));
      }
    }
    return true;
  }
}
