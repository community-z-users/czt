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
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.vcg.util.BindingFilter;
import net.sourceforge.czt.vcg.util.BindingUtils;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCConfig;
import net.sourceforge.czt.vcg.z.VCSource;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCCollector;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCNameFactory;
import net.sourceforge.czt.vcg.z.transformer.refinement.ZPredTransformerRef;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZRefKind;
import net.sourceforge.czt.z.ast.ZRefinesAnn;
import net.sourceforge.czt.z.ast.ZStateAnn;
import net.sourceforge.czt.z.ast.ZStateInfo;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;

import static net.sourceforge.czt.z.ast.ZStateInfo.*;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCCollector extends FeasibilityVCCollector implements RefinementPropertyKeys
{
  
  private ZRefKind refKind_;

  protected final Map<ZName, ZName> opsToRefineNamePairs_; // abs |-> con names
  protected final Map<ZName, ZRefKind> absOpsRefKind_;     // abs |-> refKind
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
    absOpsRefKind_ = new TreeMap<ZName, ZRefKind>(ZUtils.ZNAME_COMPARATOR);
    predTransformer_ = new ZPredTransformerRef(factory, this);
    predTransformer_.setApplyTransformer(PROP_VCG_REFINEMENT_APPLY_TRANSFORMERS_DEFAULT);

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
    setStateName(CSTATE, n);
  }
  
  protected final void setRetrieveName(ZName n)
  {
    setStateName(RETRIEVE, n);
  }

  protected boolean isRefiningIO()
  {
    return getState(RETRIEVEIN) != null
        || getState(RETRIEVEOUT) != null;
  }

  protected final void setRefKindDefault(ZRefKind v)
  {
    refKind_ = v;
  }

  protected ZRefKind getRefKindDefault()
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
    return new RefinementException(message);
  }

  @Override
  protected VCCollectionException createVCCollectionException(final String message, Throwable e)
  {
    return new RefinementException(message, e);
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
      
      if (zsii != null && zsii != NONE) {
        
        String prefixMsg = ZSTATEINFO_EXPLANATION.get(zsii);
        BindingFilter filter = getStateFilter(zsii);
        
        markStateSchema(term, termDefName, termDefGenParams, prefixMsg, zsii, filter);
        
        if (zsii == RETRIEVE) {
          
          if (getState(STATE) == null)
            throw new CztException(createVCCollectionException(
                    "No abstract state set for retrieve " + termDefName));
          else if(getState(CSTATE) == null)
            throw new CztException(createVCCollectionException(
                    "No concrete state set for retrieve " + termDefName));
  
          checkRetrieveGenParams();
          checkRetrieveBindings();
        }
        
        result = true;
      }
    }
    // otherwise, update generic params in case the state was given via section manager properties
    else if (isState(CSTATE, termDefName))
    {
      setStateGenParams(CSTATE, termDefGenParams);
    }
    else if (isState(RETRIEVE, termDefName))
    {
      setStateGenParams(RETRIEVE, termDefGenParams);
      checkRetrieveGenParams();
    }

    // If there is any refinement info, collect it for later processing
    if (term.hasAnn(ZRefinesAnn.class))
    {
      ZRefinesAnn zra = term.getAnn(ZRefinesAnn.class);
      ZName old = opsToRefineNamePairs_.put(zra.getZAbstractName(), zra.getZConcreteName());
      ZRefKind old2 = absOpsRefKind_.put(zra.getZAbstractName(), zra.getRefKind());
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
      SortedSet<Definition> asStateBindings = getBindingsFor(getState(STATE));
      SortedSet<Definition> csStateBindings = getBindingsFor(getState(CSTATE));
      // the result of getBindingsFor is unmodifiable!
      SortedSet<Definition> retrieveBindings = new TreeSet<Definition>(getBindingsFor(getState(RETRIEVE)));

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
    ZNameList retrieveGenParams_ = getStateGenParams(RETRIEVE);
    if (retrieveGenParams_ != null)
    {
      int rSize = retrieveGenParams_.size();
      ZNameList concreteStateGenParams_ = getStateGenParams(CSTATE);
      if (concreteStateGenParams_ != null)
      {
        rSize -= concreteStateGenParams_.size();
        if (!retrieveGenParams_.containsAll(concreteStateGenParams_))
          throw new CztException(createVCCollectionException(""));
      }
      ZNameList abstractStateGenParams_ = getStateGenParams(STATE);
      if (abstractStateGenParams_ != null)
      {
        rSize -= abstractStateGenParams_.size();
        if (!retrieveGenParams_.containsAll(abstractStateGenParams_))
          throw new CztException(createVCCollectionException(""));
      }
      if (rSize != 0)
      {
        final String message = "Retrieve schema '" 
            + getState(RETRIEVE)
            + "' contains '" + rSize + "' generic parameters " + "than the abstract ('"
            + getState(STATE) + "') and concrete ('"
            + getState(CSTATE)
            + "') states generic parameters put together.";
        CztLogger.getLogger(getClass()).warning(message);
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
    Pred result = predTransformer_.truePred();
    ZName concreteState_ = getState(CSTATE);
    ZNameList concreteStateGenParams_ = getStateGenParams(CSTATE);
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
          CztLogger.getLogger(getClass()).warning(message);
        }

        checkInclBindingsWithinGivenSchBindings(concreteState_, schName, relevantBindings);
        Expr schExpr;
        if (dashedState)
          schExpr = predTransformer_.createDashedSchRef(concreteState_, concreteStateGenParams_);
        else
          schExpr = predTransformer_.createSchRef(concreteState_, concreteStateGenParams_);
        result = predTransformer_.asPred(schExpr);
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
          CztLogger.getLogger(getClass()).warning(message);
          checkInclBindingsWithinGivenSchBindings(concreteState_, schName, relevantBindings);

          Expr schExpr;
          if (dashedState)
            schExpr = predTransformer_.createDashedSchRef(concreteState_, concreteStateGenParams_);
          else
            schExpr = predTransformer_.createSchRef(concreteState_, concreteStateGenParams_);
          result = predTransformer_.asPred(schExpr);
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
    ZRefKind rk = absOpsRefKind_.get(aState);
    if (rk == null) rk = getRefKindDefault();
    ZPredTransformerRef zptr = getPredTransformerRef();
    ZNameList stateGenParams = getStateGenParams(STATE);

    //assert getState(STINIT) != null && getConcreteStateInitName() != null;

    //ZName aStateInit = getState(STINIT);
    // returns whether extra state was created or not
    boolean okay = checkNeedsComplementarySchema(STINIT, CSTINIT, ZRefVCKind.INIT);
    assert getState(STINIT) == null && getState(CSTINIT) == null ||
           getState(STINIT) != null && getState(CSTINIT) != null;

    if (getState(STINIT) != null && getState(CSTINIT) != null &&
        containsRefPair(getState(STINIT), getState(CSTINIT)))
    {
      Expr absStInit = zptr.createSchRef(getState(STINIT), stateGenParams);
      Expr conStInit = zptr.createSchRef(getState(CSTINIT), getStateGenParams(CSTATE));
      Expr retrieveDashRef = zptr.createDashedSchRef(retr, getStateGenParams(RETRIEVE));

      // use RetrieveGenParams as it encompases both AS and CS; create a ConjPara for the VC as its "para"
      loc = getLocation(cState, aState);
      Pred initVC = zptr.createInitialisationVC(rk, absStInit, conStInit, retrieveDashRef);
      addRefVC(vcList, getStateSchema(CSTATE), rk, ZRefVCKind.INIT, 
          getStateGenParams(RETRIEVE), initVC, cState, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find state initialisations for neither abstract nor concrete state";
      CztLogger.getLogger(getClass()).warning(message);
    }

    // Don't use as variable as the method might change its values
    //ZName aStateFin = getState(STFIN);
    okay = checkNeedsComplementarySchema(STFIN, CSTFIN, ZRefVCKind.FIN);
    assert getState(STFIN) == null && getState(CSTFIN) == null ||
           getState(STFIN) != null && getState(CSTFIN) != null;

    // if there is any finalisation to do, create the VC for it
    if (getState(STFIN) != null && getState(CSTFIN) != null &&
        containsRefPair(getState(STFIN), getState(CSTFIN)))
    {
      Expr absStFin = zptr.createSchRef(getState(STFIN), stateGenParams);
      Expr conStFin = zptr.createSchRef(getState(CSTFIN), getStateGenParams(CSTATE));
      Expr retrieveRef = zptr.createSchRef(retr, getStateGenParams(RETRIEVE));
      loc = getLocation(getState(CSTFIN), getState(STFIN), cState, aState);
      Pred finVC = zptr.createFinalisationVC(rk, absStFin, conStFin, retrieveRef);
      addRefVC(vcList, getStateSchema(CSTATE), rk, ZRefVCKind.FIN, 
          getStateGenParams(RETRIEVE), finVC, cState, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find state finalisations for neither abstract nor concrete state";
      CztLogger.getLogger(getClass()).warning(message);
    }

    okay = checkNeedsComplementarySchema(AINITIN, CINITIN, ZRefVCKind.INIT_IN);
    assert getState(AINITIN) == null && getState(CINITIN) == null ||
           getState(AINITIN) != null && getState(CINITIN) != null;

    // if got created and we don't have a retrieve for IO, add a default one
    if (okay)
    {
      if (getState(RETRIEVEIN) == null)
      {
        final String message = "Could not find retrieve input schema. Adding a default one";
        CztLogger.getLogger(getClass()).warning(message);
      }
      if (getState(STINIT) == null)
      {
        
      }
      if (getState(CSTINIT) == null)
      {

      }
    }

    if (getState(RETRIEVEIN) != null && definitions_.containsKey(getState(RETRIEVEIN)) &&
        getState(AINITIN) != null && getState(CINITIN) != null &&
        containsRefPair(getState(AINITIN), getState(CINITIN)))
    {
      Expr absInitIn = zptr.createSchRef(getState(AINITIN), stateGenParams);
      Expr conInitIn = zptr.createSchRef(getState(CINITIN), getStateGenParams(RETRIEVEIN));
      Expr retIn =  zptr.createSchRef(getState(RETRIEVEIN), getStateGenParams(RETRIEVEIN));
      
      Pred ioInit = zptr.createInitialisationInputVC(rk, absInitIn, conInitIn, retIn);
      loc = getLocation(getState(CINITIN), getState(CSTINIT), getState(RETRIEVEIN), cState);
      addRefVC(vcList, getStateSchema(RETRIEVEIN), rk, ZRefVCKind.INIT_IN, 
          getStateGenParams(RETRIEVEIN), ioInit, getState(RETRIEVEIN), loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find initialisation schemas for neither abstract and concrete inputs";
      CztLogger.getLogger(getClass()).warning(message);
    }

    okay = checkNeedsComplementarySchema(AFINOUT, CFINOUT, ZRefVCKind.FIN_OUT);
    assert getState(AFINOUT) == null && getState(CFINOUT) == null ||
           getState(AFINOUT) != null && getState(CFINOUT) != null;

    if (okay)
    {
      if (getState(RETRIEVEOUT) == null)
      {
        final String message = "Could not find retrieve input schema. Adding a default one";
        CztLogger.getLogger(getClass()).warning(message);
      }
      if (getState(STFIN) == null)
      {

      }
      if (getState(CSTFIN) == null)
      {

      }
    }

    if (getState(RETRIEVEOUT) != null && definitions_.containsKey(getState(RETRIEVEOUT)) &&
        getState(AFINOUT) != null && getState(CFINOUT) != null &&
        containsRefPair(getState(AFINOUT), getState(CFINOUT)))
    {
      Expr absFinOut = zptr.createSchRef(getState(AFINOUT), stateGenParams);
      Expr conFinOut = zptr.createSchRef(getState(CFINOUT), getStateGenParams(RETRIEVEOUT));
      Expr retOut = zptr.createSchRef(getState(RETRIEVEOUT), getStateGenParams(RETRIEVEOUT));

      Pred ioFin  = zptr.createFinalisationOutputVC(rk, absFinOut, conFinOut, retOut);
      loc = getLocation(getState(CFINOUT), getState(CSTFIN), getState(RETRIEVEOUT), cState);
      addRefVC(vcList, getStateSchema(RETRIEVEOUT), rk, ZRefVCKind.FIN_OUT, 
          getStateGenParams(RETRIEVEOUT), ioFin, getState(RETRIEVEOUT), loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find finalisation schemas for neither abstract and concrete outputs";
      CztLogger.getLogger(getClass()).warning(message);
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
    
    ZName abs = getState(absType);
    ZName con = getState(conType);
    
    boolean result = false;
    AxPara axPara;
    if (abs != null && con == null)
    {
      switch (vckind)
      {
        case INIT:
          assert getState(CSTINIT) == null;
          con = factory_.createZName(CSTINIT.toString());
          setStateName(CSTINIT, con);
          // CSInit == [ CState' | true ]
          axPara = predTransformer_.createSchExpr(getStateGenParams(CSTATE), con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(getState(CSTATE), getStateGenParams(CSTATE))));
          break;
        case INIT_IN:
          assert getState(CINITIN) == null;
          con = factory_.createZName(CINITIN.toString());
          setStateName(CINITIN, con);
          // CInitIn == [ inputs-from-CSInit | true ]
          axPara = predTransformer_.createSchExpr(getStateGenParams(RETRIEVEIN), con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, getStateGenParams(RETRIEVEIN))));
          break;
        case FIN:
          // CSFin == [ CState | true ]
          assert getState(CSTFIN) == null;
          con = factory_.createZName(CSTFIN.toString());
          setStateName(CSTFIN, con);
          axPara = predTransformer_.createSchExpr(getStateGenParams(CSTATE), con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createSchRef(getState(CSTATE), getStateGenParams(CSTATE))));
          break;
        case FIN_OUT:
          assert getState(CFINOUT) == null;
          con = factory_.createZName(CSTINIT.toString());
          setStateName(CFINOUT, con);
          // CFinOut == [ outputs-from-CSInit | true ]
          axPara = predTransformer_.createSchExpr(getStateGenParams(RETRIEVEOUT), con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, getStateGenParams(RETRIEVEOUT))));
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
      CztLogger.getLogger(getClass()).warning(message);
      result = true;
    }
    else if (con != null && abs == null)
    {
      switch (vckind)
      {
        case INIT:
          assert getState(STINIT) == null;
          abs = factory_.createZName(CSTINIT.toString());
          setStateName(STINIT, abs);
          // ASInit == [ AState' | true ]
          axPara = predTransformer_.createSchExpr(getStateGenParams(STATE), abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(getState(STATE), getStateGenParams(STATE))));
          break;
        case INIT_IN:
          assert getState(AINITIN) == null;
          abs = factory_.createZName(CINITIN.toString());
          setStateName(AINITIN, abs);
          // AInitIn == [ inputs-from-ASInit | true ]
          axPara = predTransformer_.createSchExpr(getStateGenParams(RETRIEVEIN), abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, getStateGenParams(RETRIEVEIN))));
          break;
        case FIN:
          // ASFin == [ AState | true ]
          assert getState(STFIN) == null;
          abs = factory_.createZName(CSTFIN.toString());
          setStateName(STFIN, abs);
          axPara = predTransformer_.createSchExpr(getStateGenParams(STATE), abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createSchRef(getState(STATE), getStateGenParams(STATE))));
          break;
        case FIN_OUT:
          assert getState(AFINOUT) == null;
          abs = factory_.createZName(CSTINIT.toString());
          setStateName(AFINOUT, abs);
          // AFinOut == [ outputs-from-ASInit | true ]
          axPara = predTransformer_.createSchExpr(getStateGenParams(RETRIEVEOUT), abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, getStateGenParams(RETRIEVEOUT))));
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
      CztLogger.getLogger(getClass()).warning(message);
      result = true;
    }
    return result;
  }

  protected void calculateRefVCS(List<VC<Pred>> vcList, ZName absName, ZName conName) throws VCCollectionException
  {
    assert containsRefPair(absName, conName);

    ZRefKind rk = absOpsRefKind_.get(absName);
    if (rk == null) rk = getRefKindDefault();
    ZPredTransformerRef zptr = getPredTransformerRef();

    // states
    ZName aState  = getState(STATE);
    ZName cState  = getState(CSTATE);
    ZName retr    = getState(RETRIEVE);
    ZName retrIn  = getState(RETRIEVEIN);
    ZName retrOut = getState(RETRIEVEOUT);
    ZNameList absGenParams = getStateGenParams(STATE);
    ZNameList allGenParams = getStateGenParams(RETRIEVE);
    assert aState != null && cState != null && retr != null;

    // references
    Expr astateRef = zptr.createSchRef(aState, absGenParams);
    Expr astateDashRef = zptr.createDashedSchRef(aState, absGenParams);
    Expr cstateRef = zptr.createSchRef(cState, getStateGenParams(CSTATE));
    Expr retrieveRef = zptr.createSchRef(retr, getStateGenParams(RETRIEVE));
    Expr retrieveDashRef = zptr.createDashedSchRef(retr, getStateGenParams(RETRIEVE));

    // TODO: for now keep the given states' generic params. Later allow for IO gen params as well
    Expr absOpRef = zptr.createSchRef(absName, absGenParams);
    Expr conOpRef = zptr.createSchRef(conName, getStateGenParams(CSTATE));

    // OpSig references
    ZName absSigName = getSigSchemaName(absName);
    ZName conSigName = getSigSchemaName(conName);
    AxPara absPara = addedSigSchemas_.get(absSigName);
    AxPara conPara = addedSigSchemas_.get(conSigName);
    if (absPara == null)
      throw new VCCollectionException("Could not find added operation signature schema for " + absName);
    if (conPara == null)
      throw new VCCollectionException("Could not find added operation signature schema for " + conName);
//    RefExpr absOpSigRef = zptr.createSchRef(ZUtils.assertZName(ZUtils.getAxParaSchOrAbbrName(absPara)), absGenParams);
//    RefExpr conOpSigRef = zptr.createSchRef(ZUtils.assertZName(ZUtils.getAxParaSchOrAbbrName(conPara)), concreetStateGenParams_);
    Expr absOpSigRef = zptr.createSchRef(absSigName, absGenParams);
    Expr conOpSigRef = zptr.createSchRef(conSigName, getStateGenParams(CSTATE));


    // TODO: no IO refinement for now
    Expr retrieveInRef = null;
    Expr retrieveOutRef = null;
    if (retrIn != null)
    {
      if (retrOut == null)
      {
        // TODO: generalise this naming convention? Or use the VC name factory?
        retrOut = factory_.createZName(getState(RETRIEVE).getWord() + "RIn");
        retrieveOutRef = zptr.createSchRef(retrOut, getStateGenParams(RETRIEVEOUT));
      }
      retrieveInRef = zptr.createSchRef(retrIn, getStateGenParams(RETRIEVEIN));
    }
    if (retrOut != null)
    {
      if (retrIn == null)
      {
        retrIn = factory_.createZName(getState(RETRIEVE).getWord() + "ROut");
        // TODO shouldn't it be RETRIEVEIN here?
        retrieveInRef = zptr.createSchRef(retrIn, getStateGenParams(RETRIEVEOUT));
      }
      retrieveOutRef = zptr.createSchRef(retrOut, getStateGenParams(RETRIEVEOUT));
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

  protected void addRefVC(List<VC<Pred>> vcList, Para sourcePara, ZRefKind rk, ZRefVCKind vcrk,
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
