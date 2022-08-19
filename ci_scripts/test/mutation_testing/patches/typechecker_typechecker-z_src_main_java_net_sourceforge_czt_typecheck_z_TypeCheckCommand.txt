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

import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.session.AbstractCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.impl.SectSummaryAnn;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.WarningManager;

/**
 * A command to compute the SectTypeInfo of a Z section.
 */
public class TypeCheckCommand extends AbstractCommand
          implements TypecheckPropertiesKeys
{

  protected Boolean useBeforeDecl_ = null;
  protected Boolean recursiveTypes_ = null;
  protected Boolean useNameIds_ = null;
  protected Boolean sortDeclNames_ = null;
  protected WarningManager.WarningOutput warningOutput_ = null;
  
  @Override
  protected void processProperties(SectionManager manager)
  {
    useBeforeDecl_ = manager.hasProperty(PROP_TYPECHECK_USE_BEFORE_DECL) ?
      manager.getBooleanProperty(PROP_TYPECHECK_USE_BEFORE_DECL) : PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT;
    recursiveTypes_ = manager.hasProperty(PROP_TYPECHECK_RECURSIVE_TYPES) ?
      manager.getBooleanProperty(PROP_TYPECHECK_RECURSIVE_TYPES) : PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT;
    useNameIds_ = manager.hasProperty(PROP_TYPECHECK_USE_NAMEIDS) ?
      manager.getBooleanProperty(PROP_TYPECHECK_USE_NAMEIDS) : PROP_TYPECHECK_USE_NAMEIDS_DEFAULT;
    sortDeclNames_ = manager.hasProperty(PROP_TYPECHECK_SORT_DECL_NAMES) ?
      manager.getBooleanProperty(PROP_TYPECHECK_SORT_DECL_NAMES) : PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT;
    // will throw exception if set to something funny at section manager :-(? Catch here? Or what? TODO
    warningOutput_ = manager.hasProperty(PROP_TYPECHECK_WARNINGS_OUTPUT) ?
      WarningManager.WarningOutput.valueOf(manager.getProperty(PROP_TYPECHECK_WARNINGS_OUTPUT)) :
      PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT;
  }

  protected SectWarningsAnn processWarnings(ZSect zs, List<? extends ErrorAnn> errors)
  {
    SectWarningsAnn result;
    if (zs.hasAnn(SectWarningsAnn.class))
      result = zs.getAnn(SectWarningsAnn.class);
    else
    {
      result = SectWarningsAnn.create();
      zs.getAnns().add(result);
    }
    // if not raising warnings, remove it from the computed result.
    // since this is a SectManager TypeCheck call, then SHOW/HIDE
    // are not quite available? TODO
    if (!warningOutput_.equals(WarningManager.WarningOutput.RAISE))
    {
      Iterator<? extends ErrorAnn> it = errors.iterator();
      while (it.hasNext())
      {
        net.sourceforge.czt.typecheck.z.ErrorAnn error = it.next();
        if (error.getErrorType().equals(ErrorType.WARNING))
        {
          result.addWarning(error);
          it.remove();
        }
      }
      it = null;
    }
    return result;
  }

  protected SectSummaryAnn createSectSummaryEnv(String sectName)
  {
    return new SectSummaryAnn(sectName);
  }

  protected SectSummaryAnn summarise(SectionManager sm, ZSect zs)
  {
    SectSummaryAnn result = createSectSummaryEnv(zs.getName());
    result.generateSummary(sm, zs);
    if (zs.hasAnn(SectSummaryAnn.class))
      zs.removeAnn(SectSummaryAnn.class);
    zs.getAnns().add(result);
    return result;
  }

  protected List<? extends ErrorAnn> typecheck(Term term,
                                               SectionManager manager)
  {
    return TypeCheckUtils.typecheck(term, manager, useBeforeDecl_,
				    recursiveTypes_, useNameIds_, warningOutput_, null);
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
      SectTypeEnvAnn env = zs.getAnn(SectTypeEnvAnn.class);
      Key<SectTypeEnvAnn> typeKey = new Key<SectTypeEnvAnn>(name, SectTypeEnvAnn.class);
      if (env != null)
      {
        // this is for when the user explicitly puts the annotation, but given
        // it is within the command, it came from a get, therefore finish the transaction
        manager.endTransaction(typeKey, env);
        return false;
      }
      // perform the type check
      List<? extends ErrorAnn> errors = typecheck(zs, manager);

      // after type checking, manual or via the command, the key must be present?
      if (!manager.isCached(typeKey))
      {
        final String message = "Section " + name + " was not type checked properly. "
                + "Couldn't find its type information key in the section manager";
        throw new CommandException(manager.getDialect(), message);
      }

      // if there are warnings within the errors, add then
      SectWarningsAnn warnings = processWarnings(zs, errors);
      if (!warnings.isEmpty())
      {
        // no need for transactions above or below - directly, please 
        manager.put(new Key<SectWarningsAnn>(name, SectWarningsAnn.class), warnings, Collections.singleton(typeKey));
      }

      SectSummaryAnn summary = summarise(manager, zs);
      if (summary != null)
      {
        manager.put(new Key<SectSummaryAnn>(name, SectSummaryAnn.class), summary, Collections.singleton(typeKey));
      }
      
      // if there are remaining errors from filtered warnings raise exception
      if (!errors.isEmpty())
      {
        int count = errors.size();
        final String message = "Section " + name + " contains " + count +
          (count == 1 ? " error." : " errors.");
        Exception nestedException = new TypeErrorException(message, errors);        
        throw new CommandException(manager.getDialect(), nestedException);
      }
      traceLog("TC-TYPECHECK-OKAY");
      return true;
    }
    // these return values are kind of pointless as they are neither used, nor checked for! (Leo)
    return false;
  }
}
