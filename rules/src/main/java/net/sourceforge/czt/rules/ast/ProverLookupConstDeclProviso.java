/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.rules.ast;

import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.LookupConstDeclProvisoImpl;

/**
 * <p>A LookupConstDeclProviso used by the prover.</p>
 *
 * @author Petra Malik
 */
public class ProverLookupConstDeclProviso
  extends LookupConstDeclProvisoImpl
  implements ProverProviso
{
  private Status status_ = Status.UNCHECKED;

  public void check(SectionManager manager, String section)
  {
    try {
      Key key = new Key(section, DefinitionTable.class);
      DefinitionTable table = (DefinitionTable) manager.get(key);
      if (table != null) {
        RefExpr ref = (RefExpr) getLeftExpr();
        DefinitionTable.Definition def =
          table.lookup(ref.getZRefName().getWord());
        Expr expr = def.getExpr();
      }
    }
    catch (CommandException e) {
    }
    return;
  }

  public Status getStatus()
  {
    return status_;
  }
}
