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
package net.sourceforge.czt.vcg.z.feasibility;

import java.util.SortedSet;

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.VCG;
import net.sourceforge.czt.vcg.z.VCGUtils;
import net.sourceforge.czt.z.ast.SchemaType;

/**
 *
 * @author leo
 */
public class FeasibilityUtils 
	extends VCGUtils<//Pred
					SchemaType, SortedSet<Definition>> implements FeasibilityPropertyKeys
{

  private boolean nonEmptyGivenSets_;
  private boolean doCreateZSchemas_;

  /* CLASS SETUP METHODS */

  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected FeasibilityUtils()
  {
    super();
  }

  protected FeasibilityVCG getFeasibilityVCG()
  {
    return (FeasibilityVCG)getVCG();
  }

  @Override
  protected VCG<//Pred
  				SchemaType, SortedSet<Definition>> createVCG()
  {
    return new FeasibilityVCG();
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
    return new FeasibilityCommand();
  }

  /**
   * Top-level CZT UI tool name. e.g., "zedvcgfsb" for Z domain checks.
   * @return
   */
  @Override
  public String getToolName()
  {
    return "zedvcgfsb";
  }

  @Override
  protected void printToolUsage()
  {
    super.printToolUsage();
    System.err.println("       -g     add non-empty given set VC.");
    System.err.println("       -z     create Z schemas for precondition VC.");
  }

  @Override
  protected String printToolDefaultFlagsUsage()
  {
    return (super.printToolDefaultFlagsUsage()
              + (getFeasibilityVCG().isAddingNonemptyGivenSetVC() ? " -g " : "")
              + (getFeasibilityVCG().isCreatingZSchemas() ? " -z " : ""));
  }

  @Override
  protected boolean isKnownArg(String arg)
  {
    boolean result = "-g".equals(arg) || "-z".equals(arg);
    return result ? result : super.isKnownArg(arg);
  }

  @Override
  protected void processArg(String arg)
  {
    if (arg.equals("-g"))
      nonEmptyGivenSets_ = isKnownArg(arg);
    else if (arg.equals("-z"))
      doCreateZSchemas_ = isKnownArg(arg);
    else
      super.processArg(arg);
  }

  @Override
  protected void processCollectedProperties()
  {
    super.processCollectedProperties();
    getVCG().getManager().setProperty(
            PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS,
            String.valueOf(nonEmptyGivenSets_));
    getVCG().getManager().setProperty(
            PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS,
            String.valueOf(doCreateZSchemas_));
  }

  @Override
  protected String getVCFileNameSuffix()
  {
    return VCG_FEASIBILITY_SOURCENAME_SUFFIX;
  }

  /* UTILITY CLASS STATIC METHODS */
  private static final FeasibilityUtils feasibilityUtils_ = new FeasibilityUtils();

  public static FeasibilityUtils getFeasibilityUtils()
  {
    return feasibilityUtils_;
  }

  public static void main(String[] args)
  {
    getFeasibilityUtils().run(args);
  }
}
