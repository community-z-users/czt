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

package net.sourceforge.czt.parser.zpatt;

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;



public class JokerTableCommand
  implements Command
{
  /**
   * Creates a new joker table command.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.JokerTable.class</code>.
   */
  public JokerTableCommand()
  {
  }

  @Override
  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    Key<JokerTable> jokerKey = new Key<JokerTable>(name, JokerTable.class);
    //manager.cancelTransaction(jokerKey);

    JokerTableVisitor visitor = new JokerTableVisitor(manager);
    Key<ZSect> key = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(key);

   // manager.startTransaction(jokerKey);
    JokerTable jokerTable = (JokerTable) visitor.run(zsect);
    if (jokerTable != null)
    {
      manager.endTransaction(jokerKey, jokerTable);
            // depend on all parent tables dependencies (e.g., visitor.getDependencies) plus the ZSect
            //new DependenciesBuilder().add(visitor.getDependencies()).add(key).build());
      return true;
    }
    return false;
  }
}
