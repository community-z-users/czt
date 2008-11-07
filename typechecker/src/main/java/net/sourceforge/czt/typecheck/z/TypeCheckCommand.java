/*
  Copyright (C) 2005 Petra Malik
  Copyright (C) 2005 Tim Miller
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

package net.sourceforge.czt.typecheck.z;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * A command to compute the SectTypeInfo of a Z section.
 */
public class TypeCheckCommand
  implements Command,
             TypecheckPropertiesKeys
{
  protected List<? extends ErrorAnn> typecheck(Term term,
                                               SectionManager manager)
  {
    boolean useBeforeDecl =
      manager.getBooleanProperty(PROP_TYPECHECK_USE_BEFORE_DECL);
    boolean useNameIds =
      manager.getBooleanProperty(PROP_TYPECHECK_USE_NAMEIDS);
    boolean sortDeclNames =
      manager.getBooleanProperty(PROP_TYPECHECK_SORT_DECL_NAMES);
    boolean raiseWarnings =
      manager.getBooleanProperty(PROP_TYPECHECK_RAISE_WARNINGS);
    return TypeCheckUtils.typecheck(term, manager, useBeforeDecl, useNameIds, raiseWarnings, null);
  }

  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    // Retrieve the section information.
    // It throws an exception if it is not available.
    // This also parses the section.
    ZSect zs = (ZSect) manager.get(new Key(name, ZSect.class));
    if (zs != null) {
      //Typechecks the given section. This will include the SectTypeEnv we
      //are looking for into the manager.
      List<? extends ErrorAnn> errors = typecheck(zs, manager);
      if (! errors.isEmpty()) {
        int count = errors.size();
        String message = "Section " + name + " contains " + count +
          (count == 1 ? " error." : " errors.");
        Exception nestedException = new TypeErrorException(message, errors);
        message = "Indirect typechecking failed for section " + name +
          ". It contains type errors." + "See exception cause for details.";
        throw new CommandException(message, nestedException);
      }
    }
    return true;
  }
}
