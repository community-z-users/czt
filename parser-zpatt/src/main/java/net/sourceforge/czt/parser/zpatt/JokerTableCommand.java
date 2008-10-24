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

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

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

  public boolean compute(String name,
                         SectionManager manager)
    throws CommandException
  {
    JokerTableVisitor visitor = new JokerTableVisitor(manager);
    Key<ZSect> key = new Key<ZSect>(name, ZSect.class);
    ZSect zsect = manager.get(key);
    JokerTable jokerTable = (JokerTable) visitor.run(zsect);
    if (jokerTable != null) {
      Set dep = visitor.getDependencies();
      dep.add(key);
      manager.put(new Key<JokerTable>(name, JokerTable.class), jokerTable, dep);
      return true;
    }
    return false;
  }
}
