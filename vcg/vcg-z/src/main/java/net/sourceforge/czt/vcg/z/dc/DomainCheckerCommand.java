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

package net.sourceforge.czt.vcg.z.dc;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGCommand;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * Domain checking VCG command.
 *
 * @author leo
 */
public class DomainCheckerCommand extends VCGCommand<Pred>
{
  @Override
  protected Class<? extends VCEnvAnn<Pred>> getVCEnvAnnClass()
  {
    return DCVCEnvAnn.class;
  }

  /**
   *
   * @param zSect
   * @param manager
   * @throws VCGException
   */
  @Override
  protected VCEnvAnn<Pred> generateVCS(ZSect zSect, SectionManager manager) throws VCGException
  {
    // config the domain checker according to the given section manager 
    traceLog("DCCmd-ZSECT-CONFIG");
    DomainCheckUtils.getDCUtils().getDomainCheckVCG().setSectionManager(manager);

    // compute DCVCEnvAnn for a given ZSect:
    //    a) assume zSect is: parsed, type correct, and with all SM tables in place
    //    b) create ZSect term; adds DefTable, OpTable, etc to SM
    traceLog("DC-ZSECT-COMPUTE = " + zSect.getName());
    VCEnvAnn<Pred> result = DomainCheckUtils.getDCUtils().calculateZSectVCEnv(zSect);
    
    return result;
  }
}
