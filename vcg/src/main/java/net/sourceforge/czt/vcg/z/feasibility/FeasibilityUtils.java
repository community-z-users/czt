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

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.vcg.z.VCG;
import net.sourceforge.czt.vcg.z.VCGUtils;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author leo
 */
public class FeasibilityUtils extends VCGUtils implements FeasibilityPropertyKeys
{

  private boolean nonEmptyGivenSets_;

  /* CLASS SETUP METHODS */

  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected FeasibilityUtils()
  {
    super();
  }

  protected FeasibilityVCG getFeasibility()
  {

    return (FeasibilityVCG)getVCG();
  }

  @Override
  protected VCG<Pred> createVCG()
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
   * Top-level CZT UI tool name. e.g., "zedvcg_fsb" for Z domain checks.
   * @return
   */
  @Override
  public String getToolName()
  {
    return "zedvcg_fsb";
  }

  @Override
  protected void printToolUsage()
  {
    System.err.println("       -g     add non-empty given set VC.");
  }

  @Override
  protected String printToolDefaultFlagsUsage()
  {
    return (super.printToolDefaultFlagsUsage()
              + (getFeasibility().isAddingNonemptyGivenSetVC() ? "-g " : ""));
  }

  @Override
  protected boolean isKnownArg(String arg)
  {
    boolean result = "-g".equals(arg);
    return result ? result : super.isKnownArg(arg);
  }

  @Override
  protected void processArg(String arg)
  {
    super.processArg(arg);
    nonEmptyGivenSets_ = isKnownArg(arg);
  }

  @Override
  protected void processCollectedProperties()
  {
    getVCG().getManager().setProperty(
            PROP_VCG_FEASIBILITY_NONEMPTY_GIVENSETS,
            String.valueOf(nonEmptyGivenSets_));
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
