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

package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.session.AbstractCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * Abstract command for all VCG activities. It inherits usual abstract command 
 * and performs prior checks before any VCG can take place, namely parsing and
 * type checking a given source.
 *
 * @author Leo Freitas
 */
public abstract class VCGCommand<R> extends AbstractCommand
{

  /**
   * Parse a given resource name with the section manager
   *
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  protected ZSect parse(String name, SectionManager manager) throws CommandException
  {
    traceLog("VCG-parse = " + name);
    // parse given term - results are cached
    //Term term = manager.get(new Key<Term>(name, Term.class));
    ZSect zSect = manager.get(new Key<ZSect>(name, ZSect.class));
    return zSect;
  }

  /**
   * Type check given ZSect. Throws a CommandException in case of type errors
   *
   * @param zsect
   * @param manager
   * @return type environment for ZSect
   * @throws CommandException
   */
  protected SectTypeEnvAnn typeCheck(String name, SectionManager manager) throws CommandException
  {
    // typecheck ZSect
    traceLog("VCG-typechk = " + name);
    SectTypeEnvAnn result = manager.get(new Key<SectTypeEnvAnn>(name, SectTypeEnvAnn.class));
    return result;
  }

  /**
   * To compute VCGs we need the specification or section name.
   * It uses TermCommand to retrieve/parse the Specification/ZSection.
   * It is then type checked, and only if no problems arise, VCs are generated.
   * That is, we assume the resource to be well formed before we performing any VCG.
   * Once VCs are generated, we also type checked the VC ZSect created in the process.
   *
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  @Override
  protected boolean doCompute(String name, SectionManager manager) throws CommandException
  {
    // expect name to be a section or specification name.
    // parse and type check the name - this will update the manager if needed
    ZSect zSect = parse(name, manager);
    typeCheck(name, manager);

    // generate any necessary VCs for zSect - it must update the manager as well
    VCEnvAnn vcg = generateVCS(zSect, manager);
    assert vcg != null : "VCG/CmdException should had been thrown!";

    // just double check this is the right kind of VCEnvAnn -> DCEnvAnn
    if (!getVCEnvAnnClass().isInstance(vcg))
    {
      throw new VCGException(manager.getDialect(), "VCGCmd-WRONG-VCENVANNCLS = " + vcg.getClass().getSimpleName());
    }

    // type check resulting VC ZSection - adds SectTypeEnv to SM
    typeCheck(vcg.getVCSectName(), manager);

    // update the manager with results, depending on the kind of VCEnvAnn
    
    // NOTE: because the different kind of VCEnvAnn (e.g. DC / FSB) determine what kind
    //		 of command to use, and this is determined dynamically (e.g. getVCEnvAnnClass())
    //		 we can't put the explicit generic, but it will resolve to the appropriate kind.
    @SuppressWarnings({ "rawtypes", "unchecked" })
	Key<VCEnvAnn> vcKey = new Key/*<VCEnvAnn>*/(vcg.getOriginalZSectName(), getVCEnvAnnClass());
    manager.endTransaction(vcKey, vcg);
    
    return true;
  }

  //private <T> Key<T> createSMKey(String originalZSectName, Class<T> type)
  //{
  //  return new Key<T>(originalZSectName, type);
  //}

  /**
   * After generating VCs, the result ZSect is type checked and its VCEnvAnn
   * added to the manager with a key according to this class.
   * @return
   */
  protected abstract Class<? extends VCEnvAnn> getVCEnvAnnClass();

  /**
   * After parsing and type checking, generate VCs for the given zSect accordingly.
   * The results must update the given section manager.
   * @param zSect
   * @param manager
   * @return environment with generated VCs
   * @throws VCGException
   */
  protected abstract VCEnvAnn generateVCS(ZSect zSect, SectionManager manager) throws VCGException;
}
