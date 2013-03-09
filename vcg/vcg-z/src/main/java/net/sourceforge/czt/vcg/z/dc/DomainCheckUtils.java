/*
Copyright (C) 2004, 2006 Petra Malik
Copyright (C) 2008 Leo Freitas
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
package net.sourceforge.czt.vcg.z.dc;

import java.util.SortedSet;

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.VCG;
import net.sourceforge.czt.vcg.z.VCGUtils;
import net.sourceforge.czt.z.ast.Type2;

/**
 * Utilities for domain checking Z specifications.
 * This class provides a main method for command line use,
 * as well as several 'typecheck' methods that are designed
 * to be called by other Java classes.
 *
 * @author leo
 */
public class DomainCheckUtils extends VCGUtils<Type2, SortedSet<Definition>> implements DomainCheckPropertyKeys
{

  /* CLASS SETUP METHODS */

  private boolean isUsingInfixAppliesTo_;

  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected DomainCheckUtils()
  {
    super();
  }

  protected DomainCheckerVCG getDomainCheckVCG()
  {

    return (DomainCheckerVCG)getVCG();
  }

  @Override
  protected VCG<Type2, SortedSet<Definition>> createVCG()
  {
    return new DomainCheckerVCG();
  }

  /* UTILITY CLASS METHODS */

  /**
   * Get a Command object for use in SectionManager
   *
   * @return A command for VC generation of Z sections.
   */
  @Override
  public Command getCommand()
  {
    return new DomainCheckerCommand();
  }

  /**
   * Top-level CZT UI tool name. e.g., "zedvcgdc" for Z domain checks.
   * @return
   */
  @Override
  public String getToolName()
  {
    return "zedvcgdc";
  }

  @Override
  protected void printToolUsage()
  {
    super.printToolUsage();
    System.err.println("       -a     use infix applies to definition.");
  }

  @Override
  protected String printToolDefaultFlagsUsage()
  {
    return (super.printToolDefaultFlagsUsage()
              + (getDomainCheckVCG().isUsingInfixAppliesTo() ? "-a " : ""));
  }

  @Override
  protected boolean isKnownArg(String arg)
  {
    boolean result = "-a".equals(arg);
    return result ? result : super.isKnownArg(arg);
  }

  @Override
  protected void processArg(String arg)
  {
    if (arg.equals("-a"))
      isUsingInfixAppliesTo_ = isKnownArg(arg);
    else
      super.processArg(arg);
  }

  @Override
  protected void processCollectedProperties()
  {
    super.processCollectedProperties();
    getVCG().getManager().setProperty(
            PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO,
            String.valueOf(isUsingInfixAppliesTo_));
  }

  @Override
  protected String getVCFileNameSuffix()
  {
    return VCG_DOMAINCHECK_SOURCENAME_SUFFIX;
  }

  /* UTILITY CLASS STATIC METHODS */
  private static final DomainCheckUtils domainCheckUtils_ = new DomainCheckUtils();

  public static DomainCheckUtils getDCUtils()
  {
    return domainCheckUtils_;
  }

  public static void main(String[] args)
  {
    getDCUtils().run(args);
  }
}
