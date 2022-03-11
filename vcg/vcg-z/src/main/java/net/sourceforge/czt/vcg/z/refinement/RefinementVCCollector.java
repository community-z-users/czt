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
import java.util.TreeMap;
import java.util.TreeSet;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.vcg.util.BindingFilter;
import net.sourceforge.czt.vcg.util.BindingUtils;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCConfig;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.vcg.z.VCSource;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCCollector;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCNameFactory;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateAnn;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateInfo;
import net.sourceforge.czt.vcg.z.refinement.util.ZRefinementKind;
import net.sourceforge.czt.vcg.z.refinement.util.ZRefinesAnn;
import net.sourceforge.czt.vcg.z.transformer.refinement.ZPredTransformerRef;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCCollector extends FeasibilityVCCollector implements RefinementPropertyKeys
{
  
  private ZRefinementKind refKind_;

  protected final Map<ZName, ZName> opsToRefineNamePairs_; // abs |-> con names
  protected final Map<ZName, ZRefinementKind> absOpsRefKind_;     // abs |-> refKind
  protected final Map<ZName, Pair<Definition, AxPara>> definitions_;
  
  /**
   *
   */
  public RefinementVCCollector()
  {
    this(ZUtils.createConsoleFactory());
  }

  /** Creates a new instance of DCTerm
   * @param factory
   */
  public RefinementVCCollector(Factory factory)
  {
    super(factory);
    definitions_ = new TreeMap<ZName, Pair<Definition, AxPara>>(ZUtils.ZNAME_COMPARATOR);
    opsToRefineNamePairs_ = new TreeMap<ZName, ZName>(ZUtils.ZNAME_COMPARATOR);
    absOpsRefKind_ = new TreeMap<ZName, ZRefinementKind>(ZUtils.ZNAME_COMPARATOR);
    setPredTransformer(new ZPredTransformerRef(factory, this));
    getTransformer().setApplyTransformer(PROP_VCG_REFINEMENT_APPLY_TRANSFORMERS_DEFAULT);

    setRefKindDefault(PROP_VCG_REFINEMENT_REFKIND_DEFAULT);
    setCreateZSchemas(PROP_VCG_REFINEMENT_CREATE_ZSCHEMAS_DEFAULT);
    
    setVCNameFactory(new FeasibilityVCNameFactory(
        VCG_REFINEMENT_VCNAME_SUFFIX, VCG_REFINEMENT_SOURCENAME_SUFFIX));
  }

  protected ZPredTransformerRef getPredTransformerRef()
  {
    return (ZPredTransformerRef)getTransformer();
  }

  protected final void setConcreteStateName(ZName n)
  {
    setStateName(ZStateInfo.CSTATE, n);
  }
  
  protected final void setRetrieveName(ZName n)
  {
    setStateName(ZStateInfo.RETRIEVE, n);
  }

  protected boolean isRefiningIO()
  {
    return getStateName(ZStateInfo.RETRIEVEIN) != null
        || getStateName(ZStateInfo.RETRIEVEOUT) != null;
  }

  protected final void setRefKindDefault(ZRefinementKind v)
  {
    refKind_ = v;
  }

  protected ZRefinementKind getRefKindDefault()
  {
    return refKind_;
  }

  @Override
  protected void clearAddedPara()
  {
    super.clearAddedPara();
    opsToRefineNamePairs_.clear();
    absOpsRefKind_.clear();
    definitions_.clear();

  }

  @Override
  protected VCCollectionException createVCCollectionException(final String message)
  {
    return new RefinementException(getDialect(), message);
  }

  @Override
  protected VCCollectionException createVCCollectionException(final String message, Throwable e)
  {
    return new RefinementException(getDialect(), message, e);
  }

  @Override
  protected boolean collectStateInfo(AxPara term, Definition termDef) throws CztException
  {
    boolean result = super.collectStateInfo(term, termDef);

    ZName termDefName = termDef.getDefName();
    ZNameList termDefGenParams = termDef.getGenericParams();
    if (!result && term.hasAnn(ZStateAnn.class))
    {
      ZStateAnn zsi = term.getAnn(ZStateAnn.class);
      ZStateInfo zsii = zsi.getInfo();
      
      if (zsii != null && zsii != ZStateInfo.NONE) {
        
        String prefixMsg = zsii.getDescription();
        BindingFilter filter = getStateFilter(zsii);
        
        markStateSchema(term, termDefName, termDefGenParams, prefixMsg, zsii, filter);
        
        if (zsii == ZStateInfo.RETRIEVE) {
          
          if (getStateName(ZStateInfo.STATE) == null)
            throw new CztException(createVCCollectionException(
                    "No abstract state set for retrieve " + termDefName));
          else if(getStateName(ZStateInfo.CSTATE) == null)
            throw new CztException(createVCCollectionException(
                    "No concrete state set for retrieve " + termDefName));
  
          checkRetrieveGenParams();
          checkRetrieveBindings();
        }
        
        result = true;
      }
    }
    // otherwise, update generic params in case the state was given via section manager properties
    else if (isState(ZStateInfo.CSTATE, termDefName))
    {
      setStateGenParams(ZStateInfo.CSTATE, termDefGenParams);
    }
    else if (isState(ZStateInfo.RETRIEVE, termDefName))
    {
      setStateGenParams(ZStateInfo.RETRIEVE, termDefGenParams);
      checkRetrieveGenParams();
    }

    // If there is any refinement info, collect it for later processing
    if (term.hasAnn(ZRefinesAnn.class))
    {
      ZRefinesAnn zra = term.getAnn(ZRefinesAnn.class);
      ZName old = opsToRefineNamePairs_.put(zra.getZAbstractName(), zra.getZConcreteName());
      ZRefinementKind old2 = absOpsRefKind_.put(zra.getZAbstractName(), zra.getRefKind());
      if (old != null || old2 != null)
      {
        throw new CztException(createVCCollectionException(
                "Z refinement relationship already exists for " + ZUtils.toStringZName(zra.getZAbstractName())
                + " as " + ZUtils.toStringZName(zra.getZConcreteName())
                + " yet an old one has been found as " 
                + ZUtils.toStringZName(old)) + " with Z ref kind " + old2);
      }
    }
    return result;
  }
  
  private BindingFilter getStateFilter(ZStateInfo type) {
    switch (type) {
      case CSTATE:
      case RETRIEVE:
        return BindingUtils.STATE_FILTER;
      case CSTINIT:
        return BindingUtils.INIT_FILTER;
      case CSTFIN:
        return BindingUtils.FIN_FILTER;
      case RETRIEVEIN:
      case AINITIN:
      case CINITIN:
        return BindingUtils.INPUT_FILTER;
      case RETRIEVEOUT:
      case AFINOUT:
      case CFINOUT:
        return BindingUtils.OUTPUT_FILTER;
      default:
        throw new CztException("The state schema type " + type
            + " is unsupported, or should have been caught earlier."); 
    }
  }

  private void checkRetrieveBindings() throws CztException
  {
    boolean okay = true;
    Throwable cause = null;
    try
    {
      SortedSet<Definition> asStateBindings = getBindingsFor(getStateName(ZStateInfo.STATE));
      SortedSet<Definition> csStateBindings = getBindingsFor(getStateName(ZStateInfo.CSTATE));
      // the result of getBindingsFor is unmodifiable!
      SortedSet<Definition> retrieveBindings = new TreeSet<Definition>(getBindingsFor(getStateName(ZStateInfo.RETRIEVE)));

      // check all concrete and abstract bindings are within the retrieve
      okay = retrieveBindings.containsAll(csStateBindings) &&
             retrieveBindings.containsAll(asStateBindings);

      // if so, check that is exactly the bindings found
      if (okay)
      {
        retrieveBindings.removeAll(csStateBindings);
        retrieveBindings.removeAll(asStateBindings);
        okay = retrieveBindings.isEmpty();
      }
    }
    catch (DefinitionException ex)
    {
      okay = false;
      cause = ex;
    }

    if (!okay)
      throw new CztException(createVCCollectionException("Retrieve bindings are not the union of abstract and concrete state bindings", cause));
  }

  private void checkRetrieveGenParams() throws CztException
  {
    ZNameList retrieveGenParams_ = getStateGenParams(ZStateInfo.RETRIEVE);
    if (retrieveGenParams_ != null)
    {
      int rSize = retrieveGenParams_.size();
      ZNameList concreteStateGenParams_ = getStateGenParams(ZStateInfo.CSTATE);
      if (concreteStateGenParams_ != null)
      {
        rSize -= concreteStateGenParams_.size();
        if (!retrieveGenParams_.containsAll(concreteStateGenParams_))
          throw new CztException(createVCCollectionException(""));
      }
      ZNameList abstractStateGenParams_ = getStateGenParams(ZStateInfo.STATE);
      if (abstractStateGenParams_ != null)
      {
        rSize -= abstractStateGenParams_.size();
        if (!retrieveGenParams_.containsAll(abstractStateGenParams_))
          throw new CztException(createVCCollectionException(""));
      }
      if (rSize != 0)
      {
        final String message = "Retrieve schema '" 
            + getStateName(ZStateInfo.RETRIEVE)
            + "' contains '" + rSize + "' generic parameters " + "than the abstract ('"
            + getStateName(ZStateInfo.STATE) + "') and concrete ('"
            + getStateName(ZStateInfo.CSTATE)
            + "') states generic parameters put together.";
        getLogger().warning(message);
      }
    }
  }

  @Override
  protected void handleInclBindingsMismatch(String errorMsg)
  {
    // throw an exception in the refinement case
    throw new CztException(createVCCollectionException(errorMsg));
  }


  @Override
  protected Pred handleStateSchemaInUserDefinedSchemaPRE(ZName schName, ZNameList genParams, SortedSet<Definition> relevantBindings, boolean dashedState)
  {
    Pred result = getPredTransformerRef().truePred();
    ZName concreteState_ = getStateName(ZStateInfo.CSTATE);
    ZNameList concreteStateGenParams_ = getStateGenParams(ZStateInfo.CSTATE);
    // if this is a concrete operation for refinement, then use concrete state
    if (opsToRefineNamePairs_.containsValue(schName))
    {
      if (concreteState_ != null)
      {
        if (concreteStateGenParams_ != null && genParams != null &&
                !genParams.containsAll(concreteStateGenParams_))
        {
          final String message = "Included concretre state schema " + ZUtils.toStringZName(concreteState_) +
                " depend on generic parameters not given to concrete operation " + ZUtils.toStringZName(schName) +
                "\n\tGiven.....: " + genParams.toString() +
                "\n\tExpected..: " + concreteStateGenParams_.toString();
          getLogger().warning(message);
        }

        checkInclBindingsWithinGivenSchBindings(concreteState_, schName, relevantBindings);
        Expr schExpr;
        if (dashedState)
          schExpr = getPredTransformerRef().createDashedSchRef(concreteState_, concreteStateGenParams_);
        else
          schExpr = getPredTransformerRef().createSchRef(concreteState_, concreteStateGenParams_);
        result = getPredTransformerRef().asPred(schExpr);
      }
      // else ???? TODO: let the user give schemas as string text and parse them?
    }
    // otherwise, use the abstract state if that's the abstract operation
    // or any other operation for that matter (E.g., just use FSB handling)
    else //if (opsToRefineNamePairs_.containsKey(schName))
    {
      try
      {
        result = super.handleStateSchemaInUserDefinedSchemaPRE(schName, genParams, relevantBindings, dashedState);
      }
      catch (CztException e)
      {
        // if I can recover by trying to add CState, do it
        if (e.getCause() instanceof VCCollectionException && concreteState_ != null)
        {
          // tell the user about it.
          final String message = "An exception occurred while trying to create operation signature schema for '" + schName +
                  "'. Trying to use concrete state instead. Original message....: " + e.getCause().getMessage();
          getLogger().warning(message);
          checkInclBindingsWithinGivenSchBindings(concreteState_, schName, relevantBindings);

          Expr schExpr;
          if (dashedState)
            schExpr = getPredTransformerRef().createDashedSchRef(concreteState_, concreteStateGenParams_);
          else
            schExpr = getPredTransformerRef().createSchRef(concreteState_, concreteStateGenParams_);
          result = getPredTransformerRef().asPred(schExpr);
        }
        else
          throw e;
      }
    }
    return result;
  }

  @Override
  protected Pred handleSchema(AxPara term, Definition schDef) throws CztException
  {
    Pred result = super.handleSchema(term, schDef);

    ZName defName = schDef.getDefName();
    
    // collect definitions of interest
    //if (opsToRefineNamePairs_.containsKey(defName)
    //     ||
    //    opsToRefineNamePairs_.containsValue(defName))
    {
      Pair<Definition, AxPara> old = definitions_.put(defName, Pair.getPair(schDef, term));
      if (old != null)
      {
        throw new CztException(createVCCollectionException("Duplicated definitions are not allowed: " + defName));
      }
    }
    return result;
  }

  boolean containsRefPair(ZName absName, ZName conName)
  {
    return definitions_.containsKey(absName) &&
           definitions_.containsKey(conName);
  }

  protected void calculateRefInitFinVCS(List<VC<Pred>> vcList, ZName aState, ZName cState, ZName retr) throws VCCollectionException
  {
    assert containsRefPair(aState, cState) && definitions_.containsKey(retr);

    LocAnn loc;
    
    // TODO: refinement Kind for state as well?
    ZRefinementKind rk = absOpsRefKind_.get(aState);
    if (rk == null) rk = getRefKindDefault();
    ZPredTransformerRef zptr = getPredTransformerRef();
    ZNameList stateGenParams = getStateGenParams(ZStateInfo.STATE);

    //assert getState(ZStateInfo.STINIT) != null && getConcreteStateInitName() != null;

    //ZName aStateInit = getState(ZStateInfo.STINIT);
    // returns whether extra state was created or not
    boolean okay = checkNeedsComplementarySchema(ZStateInfo.STINIT, ZStateInfo.CSTINIT, ZRefVCKind.INIT);
    assert getStateName(ZStateInfo.STINIT) == null && getStateName(ZStateInfo.CSTINIT) == null ||
           getStateName(ZStateInfo.STINIT) != null && getStateName(ZStateInfo.CSTINIT) != null;

    if (getStateName(ZStateInfo.STINIT) != null && getStateName(ZStateInfo.CSTINIT) != null &&
        containsRefPair(getStateName(ZStateInfo.STINIT), getStateName(ZStateInfo.CSTINIT)))
    {
      Expr absStInit = zptr.createSchRef(getStateName(ZStateInfo.STINIT), stateGenParams);
      Expr conStInit = zptr.createSchRef(getStateName(ZStateInfo.CSTINIT), getStateGenParams(ZStateInfo.CSTATE));
      Expr retrieveDashRef = zptr.createDashedSchRef(retr, getStateGenParams(ZStateInfo.RETRIEVE));

      // use RetrieveGenParams as it encompases both AS and CS; create a ConjPara for the VC as its "para"
      loc = getLocation(cState, aState);
      Pred initVC = zptr.createInitialisationVC(rk, absStInit, conStInit, retrieveDashRef);
      addRefVC(vcList, getStateSchema(ZStateInfo.CSTATE), rk, ZRefVCKind.INIT, 
          getStateGenParams(ZStateInfo.RETRIEVE), initVC, cState, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find state initialisations for neither abstract nor concrete state";
      getLogger().warning(message);
    }

    // Don't use as variable as the method might change its values
    //ZName aStateFin = getState(STFIN);
    okay = checkNeedsComplementarySchema(ZStateInfo.STFIN, ZStateInfo.CSTFIN, ZRefVCKind.FIN);
    assert getStateName(ZStateInfo.STFIN) == null && getStateName(ZStateInfo.CSTFIN) == null ||
           getStateName(ZStateInfo.STFIN) != null && getStateName(ZStateInfo.CSTFIN) != null;

    // if there is any finalisation to do, create the VC for it
    if (getStateName(ZStateInfo.STFIN) != null && getStateName(ZStateInfo.CSTFIN) != null &&
        containsRefPair(getStateName(ZStateInfo.STFIN), getStateName(ZStateInfo.CSTFIN)))
    {
      Expr absStFin = zptr.createSchRef(getStateName(ZStateInfo.STFIN), stateGenParams);
      Expr conStFin = zptr.createSchRef(getStateName(ZStateInfo.CSTFIN), getStateGenParams(ZStateInfo.CSTATE));
      Expr retrieveRef = zptr.createSchRef(retr, getStateGenParams(ZStateInfo.RETRIEVE));
      loc = getLocation(getStateName(ZStateInfo.CSTFIN), getStateName(ZStateInfo.STFIN), cState, aState);
      Pred finVC = zptr.createFinalisationVC(rk, absStFin, conStFin, retrieveRef);
      addRefVC(vcList, getStateSchema(ZStateInfo.CSTATE), rk, ZRefVCKind.FIN, 
          getStateGenParams(ZStateInfo.RETRIEVE), finVC, cState, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find state finalisations for neither abstract nor concrete state";
      getLogger().warning(message);
    }

    okay = checkNeedsComplementarySchema(ZStateInfo.AINITIN, ZStateInfo.CINITIN, ZRefVCKind.INIT_IN);
    assert getStateName(ZStateInfo.AINITIN) == null && getStateName(ZStateInfo.CINITIN) == null ||
           getStateName(ZStateInfo.AINITIN) != null && getStateName(ZStateInfo.CINITIN) != null;

    // if got created and we don't have a retrieve for IO, add a default one
    if (okay)
    {
      if (getStateName(ZStateInfo.RETRIEVEIN) == null)
      {
        final String message = "Could not find retrieve input schema. Adding a default one";
        getLogger().warning(message);
      }
      if (getStateName(ZStateInfo.STINIT) == null)
      {
        
      }
      if (getStateName(ZStateInfo.CSTINIT) == null)
      {

      }
    }

    if (getStateName(ZStateInfo.RETRIEVEIN) != null && definitions_.containsKey(getStateName(ZStateInfo.RETRIEVEIN)) &&
        getStateName(ZStateInfo.AINITIN) != null && getStateName(ZStateInfo.CINITIN) != null &&
        containsRefPair(getStateName(ZStateInfo.AINITIN), getStateName(ZStateInfo.CINITIN)))
    {
      Expr absInitIn = zptr.createSchRef(getStateName(ZStateInfo.AINITIN), stateGenParams);
      Expr conInitIn = zptr.createSchRef(getStateName(ZStateInfo.CINITIN), getStateGenParams(ZStateInfo.RETRIEVEIN));
      Expr retIn =  zptr.createSchRef(getStateName(ZStateInfo.RETRIEVEIN), getStateGenParams(ZStateInfo.RETRIEVEIN));
      
      Pred ioInit = zptr.createInitialisationInputVC(rk, absInitIn, conInitIn, retIn);
      loc = getLocation(getStateName(ZStateInfo.CINITIN), getStateName(ZStateInfo.CSTINIT), getStateName(ZStateInfo.RETRIEVEIN), cState);
      addRefVC(vcList, getStateSchema(ZStateInfo.RETRIEVEIN), rk, ZRefVCKind.INIT_IN, 
          getStateGenParams(ZStateInfo.RETRIEVEIN), ioInit, getStateName(ZStateInfo.RETRIEVEIN), loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find initialisation schemas for neither abstract and concrete inputs";
      getLogger().warning(message);
    }

    okay = checkNeedsComplementarySchema(ZStateInfo.AFINOUT, ZStateInfo.CFINOUT, ZRefVCKind.FIN_OUT);
    assert getStateName(ZStateInfo.AFINOUT) == null && getStateName(ZStateInfo.CFINOUT) == null ||
           getStateName(ZStateInfo.AFINOUT) != null && getStateName(ZStateInfo.CFINOUT) != null;

    if (okay)
    {
      if (getStateName(ZStateInfo.RETRIEVEOUT) == null)
      {
        final String message = "Could not find retrieve input schema. Adding a default one";
        getLogger().warning(message);
      }
      if (getStateName(ZStateInfo.STFIN) == null)
      {

      }
      if (getStateName(ZStateInfo.CSTFIN) == null)
      {

      }
    }

    if (getStateName(ZStateInfo.RETRIEVEOUT) != null && definitions_.containsKey(getStateName(ZStateInfo.RETRIEVEOUT)) &&
        getStateName(ZStateInfo.AFINOUT) != null && getStateName(ZStateInfo.CFINOUT) != null &&
        containsRefPair(getStateName(ZStateInfo.AFINOUT), getStateName(ZStateInfo.CFINOUT)))
    {
      Expr absFinOut = zptr.createSchRef(getStateName(ZStateInfo.AFINOUT), stateGenParams);
      Expr conFinOut = zptr.createSchRef(getStateName(ZStateInfo.CFINOUT), getStateGenParams(ZStateInfo.RETRIEVEOUT));
      Expr retOut = zptr.createSchRef(getStateName(ZStateInfo.RETRIEVEOUT), getStateGenParams(ZStateInfo.RETRIEVEOUT));

      Pred ioFin  = zptr.createFinalisationOutputVC(rk, absFinOut, conFinOut, retOut);
      loc = getLocation(getStateName(ZStateInfo.CFINOUT), getStateName(ZStateInfo.CSTFIN), getStateName(ZStateInfo.RETRIEVEOUT), cState);
      addRefVC(vcList, getStateSchema(ZStateInfo.RETRIEVEOUT), rk, ZRefVCKind.FIN_OUT, 
          getStateGenParams(ZStateInfo.RETRIEVEOUT), ioFin, getStateName(ZStateInfo.RETRIEVEOUT), loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find finalisation schemas for neither abstract and concrete outputs";
      getLogger().warning(message);
    }

  }

  /**
   * If either is available, the other must be created. Like having ASFin and not CSFin.
   * Just adding it as CState' is a bad idea because of how the SchExpr/RefExpr get created.
   * @param absType
   * @param conType
   * @param vckind
   * @return
   */
//  private boolean checkNeedsComplementarySchema(ZName abs, ZName con, ZRefVCKind vckind)
  private boolean checkNeedsComplementarySchema(ZStateInfo absType, ZStateInfo conType, ZRefVCKind vckind)
  {
    
    ZName abs = getStateName(absType);
    ZName con = getStateName(conType);
    
    boolean result = false;
    AxPara axPara;
    if (abs != null && con == null)
    {
      switch (vckind)
      {
        case INIT:
          assert getStateName(ZStateInfo.CSTINIT) == null;
          con = getFactory().createZName(ZStateInfo.CSTINIT.toString());
          setStateName(ZStateInfo.CSTINIT, con);
          // CSInit == [ CState' | true ]
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.CSTATE), con,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createDashedSchRef(getStateName(ZStateInfo.CSTATE), getStateGenParams(ZStateInfo.CSTATE))));
          break;
        case INIT_IN:
          assert getStateName(ZStateInfo.CINITIN) == null;
          con = getFactory().createZName(ZStateInfo.CINITIN.toString());
          setStateName(ZStateInfo.CINITIN, con);
          // CInitIn == [ inputs-from-CSInit | true ]
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.RETRIEVEIN), con,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createDashedSchRef(null, getStateGenParams(ZStateInfo.RETRIEVEIN))));
          break;
        case FIN:
          // CSFin == [ CState | true ]
          assert getStateName(ZStateInfo.CSTFIN) == null;
          con = getFactory().createZName(ZStateInfo.CSTFIN.toString());
          setStateName(ZStateInfo.CSTFIN, con);
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.CSTATE), con,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createSchRef(getStateName(ZStateInfo.CSTATE), getStateGenParams(ZStateInfo.CSTATE))));
          break;
        case FIN_OUT:
          assert getStateName(ZStateInfo.CFINOUT) == null;
          con = getFactory().createZName(ZStateInfo.CSTINIT.toString());
          setStateName(ZStateInfo.CFINOUT, con);
          // CFinOut == [ outputs-from-CSInit | true ]
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.RETRIEVEOUT), con,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createDashedSchRef(null, getStateGenParams(ZStateInfo.RETRIEVEOUT))));
          break;
        default:
          throw new IllegalArgumentException("invalid ZRefVCKind " + vckind);
      }
      assert con != null;
      
      // mark the abstract state schema as source paragraph for the concrete state schema
      VCSource sourceInfo = new VCSource(getStateSchema(absType));
      axPara.getAnns().add(sourceInfo);
      
      addedSigSchemas_.put(con, axPara);
      final String message = "Could not find concrete schema for VC " + vckind.toString() + " generation. Creating a default one as " + con;
      getLogger().warning(message);
      result = true;
    }
    else if (con != null && abs == null)
    {
      switch (vckind)
      {
        case INIT:
          assert getStateName(ZStateInfo.STINIT) == null;
          abs = getFactory().createZName(ZStateInfo.CSTINIT.toString());
          setStateName(ZStateInfo.STINIT, abs);
          // ASInit == [ AState' | true ]
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.STATE), abs,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createDashedSchRef(getStateName(ZStateInfo.STATE), getStateGenParams(ZStateInfo.STATE))));
          break;
        case INIT_IN:
          assert getStateName(ZStateInfo.AINITIN) == null;
          abs = getFactory().createZName(ZStateInfo.CINITIN.toString());
          setStateName(ZStateInfo.AINITIN, abs);
          // AInitIn == [ inputs-from-ASInit | true ]
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.RETRIEVEIN), abs,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createDashedSchRef(null, getStateGenParams(ZStateInfo.RETRIEVEIN))));
          break;
        case FIN:
          // ASFin == [ AState | true ]
          assert getStateName(ZStateInfo.STFIN) == null;
          abs = getFactory().createZName(ZStateInfo.CSTFIN.toString());
          setStateName(ZStateInfo.STFIN, abs);
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.STATE), abs,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createSchRef(getStateName(ZStateInfo.STATE), getStateGenParams(ZStateInfo.STATE))));
          break;
        case FIN_OUT:
          assert getStateName(ZStateInfo.AFINOUT) == null;
          abs = getFactory().createZName(ZStateInfo.CSTINIT.toString());
          setStateName(ZStateInfo.AFINOUT, abs);
          // AFinOut == [ outputs-from-ASInit | true ]
          axPara = getPredTransformerRef().createSchExpr(getStateGenParams(ZStateInfo.RETRIEVEOUT), abs,
                    getPredTransformerRef().createSchemaInclusion(
                      getPredTransformerRef().createDashedSchRef(null, getStateGenParams(ZStateInfo.RETRIEVEOUT))));
          break;
        default:
          throw new IllegalArgumentException("invalid ZRefVCKind " + vckind);
      }
      assert abs != null;
      
      // mark the concrete state schema as source paragraph for the abstract state schema
      VCSource sourceInfo = new VCSource(getStateSchema(conType));
      axPara.getAnns().add(sourceInfo);
      
      addedSigSchemas_.put(abs, axPara);
      final String message = "Could not find abstract schema for VC " + vckind.toString() + " generation. Creating a default one as " + abs;
      getLogger().warning(message);
      result = true;
    }
    return result;
  }

  protected void calculateRefVCS(List<VC<Pred>> vcList, ZName absName, ZName conName) throws VCCollectionException
  {
    assert containsRefPair(absName, conName);

    ZRefinementKind rk = absOpsRefKind_.get(absName);
    if (rk == null) rk = getRefKindDefault();
    ZPredTransformerRef zptr = getPredTransformerRef();

    // states
    ZName aState  = getStateName(ZStateInfo.STATE);
    ZName cState  = getStateName(ZStateInfo.CSTATE);
    ZName retr    = getStateName(ZStateInfo.RETRIEVE);
    ZName retrIn  = getStateName(ZStateInfo.RETRIEVEIN);
    ZName retrOut = getStateName(ZStateInfo.RETRIEVEOUT);
    ZNameList absGenParams = getStateGenParams(ZStateInfo.STATE);
    ZNameList allGenParams = getStateGenParams(ZStateInfo.RETRIEVE);
    assert aState != null && cState != null && retr != null;

    // references
    Expr astateRef = zptr.createSchRef(aState, absGenParams);
    Expr astateDashRef = zptr.createDashedSchRef(aState, absGenParams);
    Expr cstateRef = zptr.createSchRef(cState, getStateGenParams(ZStateInfo.CSTATE));
    Expr retrieveRef = zptr.createSchRef(retr, getStateGenParams(ZStateInfo.RETRIEVE));
    Expr retrieveDashRef = zptr.createDashedSchRef(retr, getStateGenParams(ZStateInfo.RETRIEVE));

    // TODO: for now keep the given states' generic params. Later allow for IO gen params as well
    Expr absOpRef = zptr.createSchRef(absName, absGenParams);
    Expr conOpRef = zptr.createSchRef(conName, getStateGenParams(ZStateInfo.CSTATE));

    // OpSig references
    ZName absSigName = getSigSchemaName(absName);
    ZName conSigName = getSigSchemaName(conName);
    AxPara absPara = addedSigSchemas_.get(absSigName);
    AxPara conPara = addedSigSchemas_.get(conSigName);
    if (absPara == null)
      throw new VCCollectionException(getDialect(), "Could not find added operation signature schema for " + absName);
    if (conPara == null)
      throw new VCCollectionException(getDialect(), "Could not find added operation signature schema for " + conName);
//    RefExpr absOpSigRef = zptr.createSchRef(ZUtils.assertZName(ZUtils.getAxParaSchOrAbbrName(absPara)), absGenParams);
//    RefExpr conOpSigRef = zptr.createSchRef(ZUtils.assertZName(ZUtils.getAxParaSchOrAbbrName(conPara)), concreetStateGenParams_);
    Expr absOpSigRef = zptr.createSchRef(absSigName, absGenParams);
    Expr conOpSigRef = zptr.createSchRef(conSigName, getStateGenParams(ZStateInfo.CSTATE));


    // TODO: no IO refinement for now
    Expr retrieveInRef = null;
    Expr retrieveOutRef = null;
    if (retrIn != null)
    {
      if (retrOut == null)
      {
        // TODO: generalise this naming convention? Or use the VC name factory?
        retrOut = getFactory().createZName(getStateName(ZStateInfo.RETRIEVE).getWord() + "RIn");
        retrieveOutRef = zptr.createSchRef(retrOut, getStateGenParams(ZStateInfo.RETRIEVEOUT));
      }
      retrieveInRef = zptr.createSchRef(retrIn, getStateGenParams(ZStateInfo.RETRIEVEIN));
    }
    if (retrOut != null)
    {
      if (retrIn == null)
      {
        retrIn = getFactory().createZName(getStateName(ZStateInfo.RETRIEVE).getWord() + "ROut");
        // TODO shouldn't it be RETRIEVEIN here?
        retrieveInRef = zptr.createSchRef(retrIn, getStateGenParams(ZStateInfo.RETRIEVEOUT));
      }
      retrieveOutRef = zptr.createSchRef(retrOut, getStateGenParams(ZStateInfo.RETRIEVEOUT));
    }

    LocAnn loc = getLocation(conName, absName);

    Pred fpred = zptr.createFeasibilityVC(rk, absOpSigRef, absOpRef, conOpSigRef, conOpRef, retrieveRef, retrieveInRef);
    addRefVC(vcList, getSchemaDef(conName), rk, ZRefVCKind.APPLIC, allGenParams, fpred, conName, loc);

    Pred cpred = zptr.createCorrectnessVC(rk, astateRef, astateDashRef, absOpRef, cstateRef, conOpRef, retrieveRef, retrieveDashRef, retrieveInRef, retrieveOutRef);
    addRefVC(vcList, getSchemaDef(conName), rk, ZRefVCKind.CORRECT, allGenParams, cpred, conName, loc);
  }
  
  private AxPara getSchemaDef(ZName schName) {
    return definitions_.get(schName).getSecond();
  }

  protected LocAnn getLocation(ZName... possiblePlaces)
  {
    LocAnn loc = null;
    for(ZName name : possiblePlaces)
    {
      Pair<Definition, AxPara> pair = definitions_.get(name);
      if (pair != null)
      {
        if (pair.getSecond().hasAnn(LocAnn.class))
          loc = pair.getSecond().getAnn(LocAnn.class);
        else if (pair.getFirst().getExpr().hasAnn(LocAnn.class))
          loc = pair.getFirst().getExpr().getAnn(LocAnn.class);
        if (loc != null)
          break;
      }
    }
    return loc;
  }

  protected void addRefVC(List<VC<Pred>> vcList, Para sourcePara, ZRefinementKind rk, ZRefVCKind vcrk,
      ZNameList genParams, Pred pred, ZName opName, LocAnn loc) throws VCCollectionException
  {
    
    // create VC type out of the combination of refinement kind and VC kind
    VCConfig config = new VCConfig(vcrk.getTypeId(rk), Precedence.AFTER, genParams);
    pred.getAnns().add(config);
    
    stepVCCounter();
    VC<Pred> refVC = createVC(getVCCount(), sourcePara, VCType.NONE, pred);
    vcList.add(refVC);
  }
}
