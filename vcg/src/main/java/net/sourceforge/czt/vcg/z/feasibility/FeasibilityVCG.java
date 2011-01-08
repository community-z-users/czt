/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.vcg.z.feasibility;

import java.util.List;
import java.util.SortedSet;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.vcg.z.AbstractVCG;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollector;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.Section;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 */
public class FeasibilityVCG extends AbstractVCG<Pred> //AbstractTermVCG<List<Pair<Para, Pred>>>
        implements FeasibilityPropertyKeys
{
  private FeasibilityVCCollector fsbCheck_;
  
  /* CLASS SETUP METHOS */

  public FeasibilityVCG()
  {
    this(ZUtils.createConsoleFactory());
  }

  public FeasibilityVCG(Factory factory)
  {
    super(factory);
    fsbCheck_ = new FeasibilityVCCollector(factory);
  }

  @Override
  protected boolean defaultAddTrivialVC()
  {
    return PROP_VCG_FEASIBILITY_ADD_TRIVIAL_DC_DEFAULT;
  }

  @Override
  protected boolean defaultRaiseTypeWarnings()
  {
    return PROP_VCG_FEASIBILITY_RAISE_TYPE_WARNINGS_DEFAULT;
  }

  @Override
  protected boolean defaultProcessParents()
  {
    return PROP_VCG_FEASIBILITY_PROCESS_PARENTS_DEFAULT;
  }

  @Override
  protected boolean defaultApplyTransformers()
  {
    return PROP_VCG_FEASIBILITY_APPLY_TRANSFORMERS_DEFAULT;
  }

  @Override
  protected SortedSet<String> defaultParentsToIgnore()
  {
    SortedSet<String> result = super.defaultParentsToIgnore();
    result.add(getVCSectDefaultParentsList());
    return result;
  }

  protected boolean defaultAddingNonemptyGivenSets()
  {
    return PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS_DEFAULT;
  }

  protected boolean defaultCreatingZSchemas()
  {
    return PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS_DEFAULT;
  }

  @Override
  public VCCollector<Pred> getVCCollector()
  {
    return fsbCheck_;
  }

  /* VCG CONFIGURATION METHODS */

  public boolean isAddingNonemptyGivenSetVC()
  {
    return fsbCheck_.isAddingNonemptyGivenSetVC();
  }

  protected final void setNonemptyGivenSetVC(boolean value)
  {
    fsbCheck_.setNonemptyGivenSetVC(value);
  }

  public boolean isCreatingZSchemas()
  {
    return fsbCheck_.isCreatingZSchemas();
  }

  protected final void setCreateZSchemas(boolean value)
  {
    fsbCheck_.setCreateZSchemas(value);
  }

  @Override
  protected void doConfig() throws VCGException
  {
    super.doConfig();
    SectionManager manager = getManager();
    boolean nonEmptyGS = getManager().hasProperty(PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS) ?
          manager.getBooleanProperty(PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS) :
          defaultAddingNonemptyGivenSets();
    boolean createZS = getManager().hasProperty(PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS) ?
          manager.getBooleanProperty(PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS) :
          defaultCreatingZSchemas();
    setNonemptyGivenSetVC(nonEmptyGS);
    setCreateZSchemas(createZS);
  }

  @Override
  public void reset()
  {
    super.reset();
    setNonemptyGivenSetVC(defaultAddingNonemptyGivenSets());
    setCreateZSchemas(defaultCreatingZSchemas());
  }

  @Override
  protected void doDefaultProperties(SectionManager manager)
  {
    super.doDefaultProperties(manager);
    manager.setProperty(PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS,
            String.valueOf(defaultAddingNonemptyGivenSets()));
    manager.setProperty(PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS,
            String.valueOf(defaultCreatingZSchemas()));
  }

  /* VC CALCULATION TERM VISITING METHODS */

//  @Override
//  protected void beforeGeneratingVCG(ZSect zSect) throws VCCollectionException
//  {
//    super.beforeGeneratingVCG(zSect);
//    loadDCToolkit();
//  }

//  @Override
//  protected void afterGeneratingVCG(ZSect zSect, List<VC<Pred>> vcList) throws VCCollectionException
//  {
//    // TODO: anything to do here?
//    super.afterGeneratingVCG(zSect, vcList);
//  }

  /* VC ZSect CREATION METHODS */

  @Override
  public Class<? extends VCEnvAnn<Pred>> getVCEnvAnnClass()
  {
    return FeasibilityVCEnvAnn.class;
  }

  @Override
  protected String getVCSectName(String originalSectName)
  {
    return originalSectName + VCG_FEASIBILITY_SOURCENAME_SUFFIX;
  }

  /**
   * List of default parents for VC ZSect. For Domain check this is just "dc_toolkit".
   *
   * @return
   */
  @Override
  protected String getVCSectDefaultParentsList()
  {
    // if more than one, separate with SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR
    String result = VCG_FEASIBILITY_TOOLKIT_NAME;
    //if (needsFunctionToolkit_) TODO: add? Only needed if free types are around
    //{
    //  result += SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR;
    //  result += Section.FUNCTION_TOOLKIT.getName();
    //}
    return result;
  }

  @Override
  protected VCEnvAnn<Pred> newVCEnvAnn(String vcSectName, String originalSectName, List<VC<Pred>> vcList)
  {
    return new FeasibilityVCEnvAnn(originalSectName, vcList);
  }

  @Override
  protected ConjPara createVCConjPara(NameList genFormals, VC<Pred> vc)
  {
    return getZFactory().createConjPara(genFormals, vc.getVC());
  }

  @Override
  public void typeCheck(String sectName) throws VCGException
  {
    try
    {
      super.typeCheck(sectName);
    }
    catch (VCGException e)
    {
      // if it is a type error on the FSB section created, then warn the user
      // if it is on the user-suplied Z section, raise it as we expect type-correct input
      if (e.getCause() != null && (e.getCause() instanceof CommandException) &&
          e.getCause().getCause() != null && (e.getCause().getCause() instanceof TypeErrorException) &&
          sectName != null && sectName.endsWith(VCG_FEASIBILITY_SOURCENAME_SUFFIX))
      {
        final String msg = "\nType errors when generating feasibility VCs for Z section " +
          sectName.substring(0, sectName.length()-VCG_FEASIBILITY_SOURCENAME_SUFFIX.length()) +
          ".\nThis may happen if complex gneric types are involved.";
        logger_.info(msg);
      }
      else
      {
        throw e;
      }
    }
  }
}