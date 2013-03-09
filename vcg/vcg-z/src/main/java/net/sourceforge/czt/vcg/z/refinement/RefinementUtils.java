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

package net.sourceforge.czt.vcg.z.refinement;

import java.util.SortedSet;

import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.VCG;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityUtils;
import net.sourceforge.czt.z.ast.SchemaType;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementUtils extends FeasibilityUtils implements RefinementPropertyKeys
{

  /* CLASS SETUP METHODS */

  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected RefinementUtils()
  {
    super();
  }

  protected RefinementVCG getRefinementVCG()
  {
    return (RefinementVCG)getVCG();
  }

  @Override
  protected VCG<//Pred
  				// TODO:URGENT: should this be SchemaType, Pair<SortedSet<Definition>, SortedSet<Definition>>
  				//				to account for the two refinement mappings?
  				SchemaType, SortedSet<Definition>> createVCG()
  {
    return new RefinementVCG();
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
    return new RefinementCommand();
  }

  /**
   * Top-level CZT UI tool name. e.g., "zedvcgfsb" for Z domain checks.
   * @return
   */
  @Override
  public String getToolName()
  {
    return "zedvcgref";
  }

  @Override
  protected String getVCFileNameSuffix()
  {
    return VCG_REFINEMENT_SOURCENAME_SUFFIX;
  }

  /* UTILITY CLASS STATIC METHODS */
  private static final RefinementUtils refinementUtils_ = new RefinementUtils();

  public static RefinementUtils getRefinementUtils()
  {
    return refinementUtils_;
  }

  public static void main(String[] args)
  {
    getRefinementUtils().run(args);
  }
}
