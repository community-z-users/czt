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
import java.util.Map;
import java.util.SortedSet;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCG;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateInfo;
import net.sourceforge.czt.vcg.z.refinement.util.ZRefinementKind;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZChar;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCG extends FeasibilityVCG //AbstractTermVCG<List<Pair<Para, Pred>>>
        implements RefinementPropertyKeys
{

  private String concreteStateName_;
  private String retrieveName_;

  /* CLASS SETUP METHOS */

  public RefinementVCG()
  {
    this(ZUtils.createConsoleFactory());
  }

  public RefinementVCG(Factory factory)
  {
    super(factory);
    retrieveName_ = null;
    concreteStateName_ = null;
    fsbCheck_ = new RefinementVCCollector(factory);
    setRefKindDefault(PROP_VCG_REFINEMENT_REFKIND_DEFAULT);
    //setRefiningIO(PROP_VCG_REFINEMENT_IO_DEFAULT);
  }

  @Override
  protected String getVCGCreatedZSectTypeErrorWarningMessage(String sectName, TypeErrorException tee)
  {
    return super.getVCGCreatedZSectTypeErrorWarningMessage(sectName, tee) +
            "\nFurthermore, it might happen when Z refinement relationships are not properly set. " +
            "\nThe current concrete state name is set to '" + getRefVCCollector().getStateName(ZStateInfo.CSTATE) +
            "'; retrieve name is set to '" + getRefVCCollector().getStateName(ZStateInfo.RETRIEVE) + "'.";
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

  protected ZRefinementKind defaultRefinementKind()
  {
    return PROP_VCG_REFINEMENT_REFKIND_DEFAULT;
  }

  protected String defaultConcreteStateName()
  {
    return PROP_VCG_REFINEMENT_CONCRETE_STATE_NAME_DEFAULT;
  }

  protected String defaultRetrieveName()
  {
    return PROP_VCG_REFINEMENT_RETRIEVE_NAME_DEFAULT;
  }

  @Override
  protected void doConfig() throws VCGException
  {
    super.doConfig();
    SectionManager manager = getManager();
    String concreteSt = getManager().hasProperty(PROP_VCG_REFINEMENT_CONCRETE_STATE_NAME) ?
          manager.getProperty(PROP_VCG_REFINEMENT_CONCRETE_STATE_NAME) :
          defaultConcreteStateName();
    String ret = getManager().hasProperty(PROP_VCG_REFINEMENT_RETRIEVE_NAME) ?
          manager.getProperty(PROP_VCG_REFINEMENT_RETRIEVE_NAME) :
          defaultZStateName();
//    boolean refIo = getManager().hasProperty(PROP_VCG_REFINEMENT_IO) ?
//          manager.getBooleanProperty(PROP_VCG_REFINEMENT_IO) :
//          defaultRefiningIO();
  ZRefinementKind refKind = getManager().hasProperty(PROP_VCG_REFINEMENT_KIND) ?
		  ZRefinementKind.valueOf(manager.getProperty(PROP_VCG_REFINEMENT_KIND)) :
          defaultRefinementKind();
    setConcreteStateName(concreteSt);
    setRetrieveName(ret);
    //setRefiningIO(refIo);
    setRefKindDefault(refKind);
  }

  @Override
  public void reset()
  {
    super.reset();
    setConcreteStateName(null);
    setRetrieveName(null);
    //setRefiningIO(defaultRefiningIO());
    setRefKindDefault(defaultRefinementKind());
  }

  @Override
  protected void doDefaultProperties(SectionManager manager)
  {
    super.doDefaultProperties(manager);
    manager.setProperty(PROP_VCG_REFINEMENT_CONCRETE_STATE_NAME,
            String.valueOf(defaultConcreteStateName()));
    manager.setProperty(PROP_VCG_REFINEMENT_RETRIEVE_NAME,
            String.valueOf(defaultRetrieveName()));
//    manager.setProperty(PROP_VCG_REFINEMENT_IO,
//            String.valueOf(defaultRefiningIO()));
    manager.setProperty(PROP_VCG_REFINEMENT_KIND,
            String.valueOf(defaultRefinementKind()));
  }

  protected RefinementVCCollector getRefVCCollector()
  {
    return (RefinementVCCollector)getVCCollector();
  }

  /* VCG CONFIGURATION METHODS */

  /* VC ZSect CREATION METHODS */

  @Override
  public Class<? extends VCEnvAnn> getVCEnvAnnClass()
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
  protected VCEnvAnn newVCEnvAnn(String vcSectName, String originalSectName, List<VC<Pred>> vcList)
  {
    // Or get the getVCCollector().getVCNameFactory()?
    return new RefinementVCEnvAnn(originalSectName, vcList, getVCCollector().getVCNameFactory());
  }

  protected void setConcreteStateName(String name)
  {
    if (name != null && !name.isEmpty())
    {
      if (name.indexOf(ZChar.PRIME.toString()) != -1 || name.indexOf("'") != -1)
        throw new CztException(new RefinementException(getDialect(), "Cannot set Z concrete state name that contains prime decoration"));
      concreteStateName_ = name;
      getRefVCCollector().setConcreteStateName(getFactory().createZName(name));
    }
    else
    {
      concreteStateName_ = null;
      getRefVCCollector().setConcreteStateName(null);
    }
  }

  protected void setRetrieveName(String name)
  {
    if (name != null && !name.isEmpty())
    {
      if (name.indexOf(ZChar.PRIME.toString()) != -1 || name.indexOf("'") != -1)
        throw new CztException(new RefinementException(getDialect(), "Cannot set Z retrieve schema name that contains prime decoration"));
      retrieveName_ = name;
      getRefVCCollector().setRetrieveName(getFactory().createZName(name));
    }
    else
    {
      retrieveName_ = null;
      getRefVCCollector().setConcreteStateName(null);
    }
  }

  // TODO: add RIn, ROut, CIn, AIn, CFin, AFin from properties?
  
//  protected final void setRefiningIO(boolean v)
//  {
////    getRefVCCollector().setRefiningIO(v);
//  }

  protected final void setRefKindDefault(ZRefinementKind v)
  {
    getRefVCCollector().setRefKindDefault(v);
    
  }

  @Override
  protected void beforeGeneratingVCG(ZSect zSect) throws VCCollectionException
  {
    super.beforeGeneratingVCG(zSect);
    assert getVCCollector() instanceof RefinementVCCollector;

    assert getRefVCCollector().getStateName(ZStateInfo.CSTATE) == null;
    assert getRefVCCollector().getStateName(ZStateInfo.RETRIEVE) == null;

    // in case the user explicitly define the Z state name
    if (concreteStateName_ != null)
      setConcreteStateName(concreteStateName_);

    if (retrieveName_ != null)
      setRetrieveName(retrieveName_);
  }

  @Override
  protected void afterGeneratingVCG(ZSect zSect, List<VC<Pred>> vcList) throws VCCollectionException
  {
    super.afterGeneratingVCG(zSect, vcList);

    RefinementVCCollector rvcc = getRefVCCollector();
    Map<ZName, Pair<Definition, AxPara>> defsOfInterest = rvcc.definitions_;
    Map<ZName, ZName> opRefPairs = rvcc.opsToRefineNamePairs_;

    assert defsOfInterest != null && opRefPairs != null;

    // if there are any refinement relationships
    if (!opRefPairs.isEmpty())
    {
      // we ought to have found at least twice as many definitions of interest + AState + CState
      assert ((opRefPairs.size() * 2) + 2 <= defsOfInterest.size());

      ZName aState = rvcc.getStateName(ZStateInfo.STATE);
      ZName cState = rvcc.getStateName(ZStateInfo.CSTATE);
      ZName retr = rvcc.getStateName(ZStateInfo.RETRIEVE);

      // if we have any ref pair / def of interest information and not state/retrieve, raise an error
      if (aState == null || cState == null || retr == null)
      {
        throw new VCCollectionException(getDialect(), "Inconsistent Z refinement relationship definitions. The abstract state '"
                + aState + "', the concrete state '" + cState + " and the retrieve schema '" + retr + "' must all be non-null "
                + " in order to generate VCs for " + defsOfInterest.size() + " definitions of interest.");
      }
      // add the init / finalisation VCs
      rvcc.calculateRefInitFinVCS(vcList, aState, cState, retr);

      // for all opRef pairs, create extra VCs
      for(Map.Entry<ZName, ZName> pair : opRefPairs.entrySet())
      {
        ZName absName = pair.getKey();
        ZName conName = pair.getValue();
        // we must habve come across definition of both AOp and COp
        if (rvcc.containsRefPair(absName, conName))
        {
          rvcc.calculateRefVCS(vcList, absName, conName);
        }
        // otherwise VCG missed something during collection
        else
        {
          throw new VCCollectionException(getDialect(), "Could not find definition for Z refinement relationship between operations.\n\tAbstract..: '"
                  + absName + "'\n\tConcrete..: '" + conName + "'");
        }
      }
    }
  }
}
