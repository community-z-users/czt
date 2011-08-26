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
import net.sourceforge.czt.session.AbstractCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.WarningManager;

/**
 * A command to compute the SectTypeInfo of a Z section.
 */
public class TypeCheckCommand extends AbstractCommand
          implements TypecheckPropertiesKeys
{
  protected List<? extends ErrorAnn> typecheck(Term term,
                                               SectionManager manager)
  {
    boolean useBeforeDecl =
      manager.getBooleanProperty(PROP_TYPECHECK_USE_BEFORE_DECL);
    boolean recursiveTypes =
      manager.getBooleanProperty(PROP_TYPECHECK_RECURSIVE_TYPES);
    boolean useNameIds =
      manager.getBooleanProperty(PROP_TYPECHECK_USE_NAMEIDS);
    boolean sortDeclNames =
      manager.getBooleanProperty(PROP_TYPECHECK_SORT_DECL_NAMES);
    String warningOutput = manager.getProperty(PROP_TYPECHECK_WARNINGS_OUTPUT);
    if (warningOutput == null || warningOutput.isEmpty())
    {
      warningOutput = PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT.toString();
    }
    return TypeCheckUtils.typecheck(term, manager, useBeforeDecl,
				    recursiveTypes, useNameIds,
        WarningManager.WarningOutput.valueOf(warningOutput), null);
  }


  /**
   * This command type checks the given ZSection name, providing no parsing
   * or resource Source location error occur. If the ZSect is not yet cached,
   * it gets parsed. It raises an exception
   * type errors, if they exist.
   *
   * -pre name is of a ZSect
   * -pre ZSect has no parsing error
   * @param name ZSect name
   * @param manager
   * @return irrelevant (!)
   * @throws CommandException if named resource Source cannot be located, or if
   *    named ZSect has a parsing or type checking error.
   */
  @Override
  protected boolean doCompute(String name, SectionManager manager)
    throws CommandException
  {
    // Retrieve the section information.
    // It throws an exception if it is not available.
    // This also parses the section.
    traceLog("TC-RETRIEVE-ZSECT = " + name);
    ZSect zs = manager.get(new Key<ZSect>(name, ZSect.class));
    if (zs != null) {
      //Typechecks the given section. This will include the SectTypeEnv we
      //are looking for into the manager.
      List<? extends ErrorAnn> errors = typecheck(zs, manager);
      if (! errors.isEmpty()) {
        int count = errors.size();
        final String message = "Section " + name + " contains " + count +
          (count == 1 ? " error." : " errors.");
        Exception nestedException = new TypeErrorException(message, errors);        
        throw new CommandException(nestedException);
      }
      traceLog("TC-TYPECHECK-OKAY");
      return true;
    }
    // these return values are kind of pointless as they are neither used, nor checked for! (Leo)
    return false;
  }
}
