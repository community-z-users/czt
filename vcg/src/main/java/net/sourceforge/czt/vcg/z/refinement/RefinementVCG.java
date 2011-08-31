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

import java.util.List;
import java.util.SortedSet;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCG;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCG extends FeasibilityVCG //AbstractTermVCG<List<Pair<Para, Pred>>>
        implements RefinementPropertyKeys
{
  /* CLASS SETUP METHOS */

  public RefinementVCG()
  {
    this(ZUtils.createConsoleFactory());
  }

  public RefinementVCG(Factory factory)
  {
    super(factory);
    fsbCheck_ = new RefinementVCCollector(factory);
  }

  @Override
  protected String getFSBSourceNameSuffix()
  {
    return VCG_REFINEMENT_SOURCENAME_SUFFIX;
  }

  @Override
  protected boolean defaultAddTrivialVC()
  {
    return PROP_VCG_REFINEMENT_ADD_TRIVIAL_VC_DEFAULT;
  }

  @Override
  protected boolean defaultRaiseTypeWarnings()
  {
    return PROP_VCG_REFINEMENT_RAISE_TYPE_WARNINGS_DEFAULT;
  }

  @Override
  protected boolean defaultProcessParents()
  {
    return PROP_VCG_REFINEMENT_PROCESS_PARENTS_DEFAULT;
  }

  @Override
  protected boolean defaultApplyTransformers()
  {
    return PROP_VCG_REFINEMENT_APPLY_TRANSFORMERS_DEFAULT;
  }

  @Override
  protected SortedSet<String> defaultParentsToIgnore()
  {
    SortedSet<String> result = super.defaultParentsToIgnore();
    result.add(getVCSectDefaultParentsList());
    return result;
  }

  @Override
  protected boolean defaultCreatingZSchemas()
  {
    return PROP_VCG_REFINEMENT_CREATE_ZSCHEMAS_DEFAULT;
  }

  @Override
  protected String defaultZStateName()
  {
    return PROP_VCG_REFINEMENT_ZSTATE_NAME_DEFAULT;
  }

  protected RefinementVCCollector getRefVCCollector()
  {
    return (RefinementVCCollector)getVCCollector();
  }

  /* VCG CONFIGURATION METHODS */

  /* VC ZSect CREATION METHODS */

  @Override
  public Class<? extends VCEnvAnn<Pred>> getVCEnvAnnClass()
  {
    return RefinementVCEnvAnn.class;
  }

  /**
   * List of default parents for VC ZSect. For Domain check this is just "dc_toolkit".
   *
   * @return
   */
  @Override
  protected String getVCSectDefaultParentsList()
  {
    return VCG_REFINEMENT_TOOLKIT_NAME;
  }

  @Override
  protected VCEnvAnn<Pred> newVCEnvAnn(String vcSectName, String originalSectName, List<VC<Pred>> vcList)
  {
    // Or get the getVCCollector().getVCNameFactory()?
    return new RefinementVCEnvAnn(originalSectName, vcList, getVCNameFactory());
  }
}
