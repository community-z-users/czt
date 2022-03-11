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

import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.util.DefinitionTable;
import net.sourceforge.czt.vcg.z.AbstractVCG;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCCollector;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateInfo;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZChar;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 */
public class FeasibilityVCG extends 
		AbstractVCG<//Pred, 
					SchemaType, SortedSet<Definition>> //AbstractTermVCG<List<Pair<Para, Pred>>>
        implements FeasibilityPropertyKeys
{
  protected FeasibilityVCCollector fsbCheck_;
  private String zStateName_;
  
  /* CLASS SETUP METHOS */

  public FeasibilityVCG()
  {
    this(ZUtils.createConsoleFactory());
  }

  public FeasibilityVCG(Factory factory)
  {
    super(factory);
    zStateName_ = null;
    fsbCheck_ = new FeasibilityVCCollector(factory);
  }

  @Override
  protected boolean defaultAddTrivialVC()
  {
    return PROP_VCG_FEASIBILITY_ADD_TRIVIAL_VC_DEFAULT;
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

  protected String defaultZStateName()
  {
    return PROP_VCG_FEASIBILITY_ZSTATE_NAME_DEFAULT;
  }

  @Override
  public final VCCollector<//Pred
  						SchemaType, SortedSet<Definition>> getVCCollector()
  {
    return fsbCheck_;
  }

  public FeasibilityVCCollector getFSBVCCollector()
  {
    return (FeasibilityVCCollector)getVCCollector();
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
    String zstate = getManager().hasProperty(PROP_VCG_FEASIBILITY_ZSTATE_NAME) ?
          manager.getProperty(PROP_VCG_FEASIBILITY_ZSTATE_NAME) :
          defaultZStateName();
    setNonemptyGivenSetVC(nonEmptyGS);
    setCreateZSchemas(createZS);
    setZStateName(zstate);
  }

  @Override
  public void reset()
  {
    super.reset();
    setZStateName(null);
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
    manager.setProperty(PROP_VCG_FEASIBILITY_ZSTATE_NAME,
            String.valueOf(defaultZStateName()));
  }

  protected void setZStateName(String name)
  {
    if (name != null && !name.isEmpty())
    {
      if (name.indexOf(ZChar.PRIME.toString()) != -1 || name.indexOf('\'') != -1)
        throw new CztException(new FeasibilityException(getDialect(), "Cannot set Z state name that contains prime decoration"));
      zStateName_ = name;
      getFSBVCCollector().setStateName(ZStateInfo.STATE, getFactory().createZName(name));
    }
    else
    {
      zStateName_ = null;
      getFSBVCCollector().setStateName(ZStateInfo.STATE, null);
    }
  }

  /* VC CALCULATION TERM VISITING METHODS */

  @Override
  protected void beforeGeneratingVCG(ZSect zSect) throws VCCollectionException
  {
    super.beforeGeneratingVCG(zSect);
    assert getVCCollector() instanceof FeasibilityVCCollector;

    // this sets the ZState name within the collector to null.
    getFSBVCCollector().clearAddedPara();
    assert getFSBVCCollector().getStateName(ZStateInfo.STATE) == null;

    // in case the user explicitly define the Z state name 
    if (zStateName_ != null)
      setZStateName(zStateName_);
  }

  /* VC ZSect CREATION METHODS */

  @Override
  public Class<? extends VCEnvAnn> getVCEnvAnnClass()
  {
    return FeasibilityVCEnvAnn.class;
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
  protected VCEnvAnn newVCEnvAnn(String vcSectName, String originalSectName, List<VC<Pred>> vcList)
  {
    // Or get the getVCCollector().getVCNameFactory()?
    return new FeasibilityVCEnvAnn(originalSectName, vcList, getVCCollector().getVCNameFactory());
  }

  @Override
  protected ConjPara createVCConjPara(NameList genFormals, VC<Pred> vc)
  {
    return getFactory().createConjPara(genFormals, vc.getVC());
  }

  @Override
  public void typeCheck(String sectName, boolean sourceSect) throws VCGException
  {
    try
    {
      super.typeCheck(sectName, sourceSect);
    }
    catch (VCGException e)
    {
      // if it is a type error on the FSB section created, then warn the user
      // if it is on the user-suplied Z section, raise it as we expect type-correct input
      if (!sourceSect && e.getCause() != null && (e.getCause() instanceof CommandException) &&
          e.getCause().getCause() != null && (e.getCause().getCause() instanceof TypeErrorException) &&
          sectName != null)
      {
        final String msg = getVCGCreatedZSectTypeErrorWarningMessage(sectName, (TypeErrorException)e.getCause().getCause());
        getLogger().severe(msg);
      }
      else
      {
        throw e;
      }
    }
  }

  @Override
  protected void afterGeneratingVCG(ZSect zSect, List<VC<Pred>> vcList) throws VCCollectionException
  {
    super.afterGeneratingVCG(zSect, vcList);
    getFSBVCCollector().createStateVCS(vcList);
  }

  protected String getVCGCreatedZSectTypeErrorWarningMessage(String sectName, TypeErrorException tee)
  {
    return "\nType errors on " + getClass().getSimpleName() + " for Z section " + sectName +
          ".\n\t" + printTypeErrors(tee).toString() +
          ".\nThis may happen if complex gneric types are involved" +
          (isCreatingZSchemas() ? " or the state schema (i.e., '"
          + getFSBVCCollector().getStateName(ZStateInfo.STATE)  + "') is not properly set.": ".");
  }

  @Override
  protected boolean isTableMandatory(Key<? extends InfoTable> key)
  {
    // for Feasibility, both tables are mandatory.
    return key.getType().isAssignableFrom(DefinitionTable.class) ||
           key.getType().isAssignableFrom(OpTable.class);
  }

  @Override
  protected boolean shouldTryTableAgain(Key<? extends InfoTable> key)
  {
    return false; // for Feasibility, never try again, whatever the table
  }
}
