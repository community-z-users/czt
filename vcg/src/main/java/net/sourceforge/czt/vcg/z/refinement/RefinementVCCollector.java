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
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.vcg.util.BindingUtils;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCCollector;
import net.sourceforge.czt.vcg.z.transformer.refinement.ZPredTransformerRef;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
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

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCCollector extends FeasibilityVCCollector implements RefinementPropertyKeys
{
  private ZName concreteState_;
  private ZName concreteStateInit_;
  private ZName concreteStateFin_;
  private ZName abstractStateInitIn_;
  private ZName abstractStateFinOut_;
  private ZName concreteStateInitIn_;
  private ZName concreteStateFinOut_;

  private ZName retrieve_;
  private ZName retrieveIn_;
  private ZName retrieveOut_;
  private ZNameList concreetStateGenParams_;
  private ZNameList retrieveGenParams_;
  private ZNameList retrieveInGenParams_;
  private ZNameList retrieveOutGenParams_;
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

    setConcreteStateName(null);
    setConcreteStateInitName(null);
    setConcreteStateFinName(null);
    setAbstractStateInitIn(null);
    setAbstractStateFinOut(null);
    setConcreteStateInitIn(null);
    setConcreteStateFinOut(null);
    setRetrieveName(null);
    setRetrieveInName(null);
    setRetrieveOutName(null);

    setRefKindDefault(PROP_VCG_REFINEMENT_REFKIND_DEFAULT);
    setCreateZSchemas(PROP_VCG_REFINEMENT_CREATE_ZSCHEMAS_DEFAULT);
  }

  protected final void setConcreteStateName(ZName n)
  {
    concreteState_ = n;
    concreetStateGenParams_ = null;
  }

  protected final void setConcreteStateInitName(ZName n)
  {
    concreteStateInit_ = n;
  }

  protected final void setConcreteStateFinName(ZName n)
  {
    concreteStateFin_ = n;
  }

  protected final void setAbstractStateInitIn(ZName n)
  {
    abstractStateInitIn_ = n;
  }

  protected final void setAbstractStateFinOut(ZName n)
  {
    abstractStateFinOut_ = n;
  }

  protected final void setConcreteStateInitIn(ZName n)
  {
    concreteStateInitIn_ = n;
  }

  protected final void setConcreteStateFinOut(ZName n)
  {
    concreteStateFinOut_ = n;
  }

  protected ZPredTransformerRef getPredTransformerRef()
  {
    return (ZPredTransformerRef)getTransformer();
  }

  public ZName getConcreteStateName()
  {
    return concreteState_;
  }

  public ZName getConcreteStateInitName()
  {
    return concreteStateInit_;
  }

  public ZNameList getConcreteStateGenParams()
  {
    return concreetStateGenParams_;
  }

  protected final void setRetrieveName(ZName n)
  {
    retrieve_ = n;
    retrieveGenParams_ = null;
  }

  protected final void setRetrieveInName(ZName n)
  {
    retrieveIn_ = n;
    retrieveInGenParams_ = null;
  }

  protected final void setRetrieveOutName(ZName n)
  {
    retrieveOut_ = n;
    retrieveOutGenParams_ = null;
  }

  public ZName getRetrieveName()
  {
    return retrieve_;
  }

  public ZName getRetrieveInName()
  {
    return retrieveIn_;
  }

  public ZName getRetrieveOutName()
  {
    return retrieveOut_;
  }

  public ZNameList getRetrieveGenParams()
  {
    return retrieveGenParams_;
  }

  public ZNameList getRetrieveInGenParams()
  {
    return retrieveInGenParams_;
  }

  public ZNameList getRetrieveOutGenParams()
  {
    return retrieveOutGenParams_;
  }

  protected boolean isRefiningIO()
  {
    return retrieveIn_ != null || retrieveOut_ != null;
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
    setConcreteStateName(null);
    setConcreteStateInitName(null);
    setConcreteStateFinName(null);
    setAbstractStateInitIn(null);
    setAbstractStateFinOut(null);
    setConcreteStateInitIn(null);
    setConcreteStateFinOut(null);
    setRetrieveName(null);
    setRetrieveInName(null);
    setRetrieveOutName(null);
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

  public interface VCNameSuffix
  {
    public String getVCNameSuffix();
  }

  @Override
  public VC<Pred> createVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException
  {
    VCNameSuffix ns = term.getAnn(VCNameSuffix.class);
    if (getVCNameFactory() != null)
      if (ns != null)
        return new RefinementVC(vcId, term, type, vc, getVCNameFactory(), ns.getVCNameSuffix());
      else
        return new RefinementVC(vcId, term, type, vc, getVCNameFactory());
    else
      if (ns != null)
        return new RefinementVC(vcId,term, type, vc, ns.getVCNameSuffix());
      else
        return new RefinementVC(vcId, term, type, vc);
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
      final String prefixMsg = ZSTATEINFO_EXPLANATION.get(zsii);
      if (zsii.equals(ZStateInfo.CSTATE))
      {
        checkPreviousState(prefixMsg, concreteState_, termDefName);
        setConcreteStateName(termDefName);
        concreetStateGenParams_ = termDefGenParams;
        checkStateBindings(prefixMsg, concreteState_);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.CSTINIT))
      {
        checkPreviousState(prefixMsg, concreteStateInit_, termDefName);
        setConcreteStateInitName(termDefName);
        // assuming the generic parameters are just like the concrete state's
        checkStateBindings(prefixMsg, concreteStateInit_, BindingUtils.DASHED_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.CSTFIN))
      {
        checkPreviousState(prefixMsg, concreteStateFin_, termDefName);
        setConcreteStateFinName(termDefName);
        // assuming the generic parameters are just like the concrete state's
        checkStateBindings(prefixMsg, concreteStateFin_, BindingUtils.STATE_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.RETRIEVE))
      {
        checkPreviousState(prefixMsg, retrieve_, termDefName);

        if (getStateSchema() == null)
          throw new CztException(createVCCollectionException(
                  "No abstract state set for retrieve " + retrieve_));
        else if(concreteState_ == null)
          throw new CztException(createVCCollectionException(
                  "No concrete state set for retrieve " + retrieve_));

        setRetrieveName(termDefName);
        retrieveGenParams_ = termDefGenParams;

        checkStateBindings(prefixMsg, retrieve_);
        checkRetrieveGenParams();
        checkRetrieveBindings();
        result = true;
      }
      else if (zsii.equals(ZStateInfo.RETRIEVEIN))
      {
        checkPreviousState(prefixMsg, retrieveIn_, termDefName);
        // assuming the same as retrieve gen params
        setRetrieveInName(termDefName);
        checkStateBindings(prefixMsg, retrieveIn_, BindingUtils.INPUT_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.RETRIEVEOUT))
      {
        checkPreviousState(prefixMsg, retrieveOut_, termDefName);
        // assuming the same as retrieve gen params
        setRetrieveOutName(termDefName);
        checkStateBindings(prefixMsg, retrieveOut_, BindingUtils.OUTPUT_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.AINITIN))
      {
        checkPreviousState(prefixMsg, abstractStateInitIn_, termDefName);
        // assuming the same as retrieve gen params
        setAbstractStateInitIn(termDefName);
        checkStateBindings(prefixMsg, abstractStateInitIn_, BindingUtils.INPUT_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.CINITIN))
      {
        checkPreviousState(prefixMsg, concreteStateInitIn_, termDefName);
        // assuming the same as retrieve gen params
        setConcreteStateInitIn(termDefName);
        checkStateBindings(prefixMsg, concreteStateInitIn_, BindingUtils.INPUT_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.AFINOUT))
      {
        checkPreviousState(prefixMsg, abstractStateFinOut_, termDefName);
        // assuming the same as retrieve gen params
        setAbstractStateFinOut(termDefName);
        checkStateBindings(prefixMsg, abstractStateFinOut_, BindingUtils.INPUT_FILTER);
        result = true;
      }
      else if (zsii.equals(ZStateInfo.CFINOUT))
      {
        checkPreviousState(prefixMsg, concreteStateFinOut_, termDefName);
        // assuming the same as retrieve gen params
        setConcreteStateFinOut(concreteStateFinOut_);
        checkStateBindings(prefixMsg, concreteStateFinOut_, BindingUtils.INPUT_FILTER);
        result = true;
      }
    }
    // otherwise, update generic params in case the state was given via section manager properties
    else if (concreteState_ != null && ZUtils.namesEqual(termDefName, concreteState_))
    {
      concreetStateGenParams_ = termDefGenParams;
    }
    else if (retrieve_ != null && ZUtils.namesEqual(termDefName, retrieve_))
    {
      retrieveGenParams_ = termDefGenParams;
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

  private void checkRetrieveBindings() throws CztException
  {
    boolean okay = true;
    Throwable cause = null;
    try
    {
      SortedSet<Definition> asStateBindings = getDefTable().bindings(getStateSchema());
      SortedSet<Definition> csStateBindings = getDefTable().bindings(concreteState_);
      SortedSet<Definition> retrieveBindings = getDefTable().bindings(retrieve_);

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
    if (retrieveGenParams_ != null)
    {
      int rSize = retrieveGenParams_.size();
      if (concreetStateGenParams_ != null)
      {
        rSize -= concreetStateGenParams_.size();
        if (!retrieveGenParams_.containsAll(concreetStateGenParams_))
          throw new CztException(createVCCollectionException(""));
      }
      if (getStateSchemaGenParams() != null)
      {
        rSize -= getStateSchemaGenParams().size();
        if (!retrieveGenParams_.containsAll(getStateSchemaGenParams()))
          throw new CztException(createVCCollectionException(""));
      }
      if (rSize != 0)
      {
        final String message = "Retrieve schema '" + retrieve_ + "' contains '" + rSize + "' generic parameters "
                + "than the abstract ('" + getStateSchema() + "') and concrete ('" +
                concreteState_ + "') states generic parameters put together.";
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
  protected Pred handleStateSchemaInUserDefinedSchemaPRE(ZName schName, ZNameList genParams, SortedSet<Definition> beforeBindings)
  {
    Pred result = predTransformer_.truePred();
    // if this is a concrete operation for refinement, then use concrete state
    if (opsToRefineNamePairs_.containsValue(schName))
    {
      if (concreteState_ != null)
      {
        if (concreetStateGenParams_ != null && genParams != null &&
                !genParams.containsAll(concreetStateGenParams_))
        {
          final String message = "Included concretre state schema " + ZUtils.toStringZName(concreteState_) +
                " depend on generic parameters not given to concrete operation " + ZUtils.toStringZName(schName) +
                "\n\tGiven.....: " + genParams.toString() +
                "\n\tExpected..: " + concreetStateGenParams_.toString();
          CztLogger.getLogger(getClass()).warning(message);
        }

        checkInclBindingsWithinGivenSchBindings(concreteState_, schName, beforeBindings);
        result = predTransformer_.asPred(predTransformer_.createSchRef(concreteState_, concreetStateGenParams_));
      }
      // else ???? TODO: let the user give schemas as string text and parse them?
    }
    // otherwise, use the abstract state if that's the abstract operation
    // or any other operation for that matter (E.g., just use FSB handling)
    else //if (opsToRefineNamePairs_.containsKey(schName))
    {
      try
      {
        result = super.handleStateSchemaInUserDefinedSchemaPRE(schName, genParams, beforeBindings);
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
          checkInclBindingsWithinGivenSchBindings(concreteState_, schName, beforeBindings);
          result = predTransformer_.asPred(predTransformer_.createSchRef(concreteState_, concreetStateGenParams_));
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
    ZNameList stateGenParams = getStateSchemaGenParams();

    //assert getStateInitSchema() != null && getConcreteStateInitName() != null;

    //ZName aStateInit = getStateInitSchema();
    // returns whether extra state was created or not
    boolean okay = checkNeedsComplementarySchema(getStateInitSchema(), concreteStateInit_, ZRefVCKind.Initialisation);
    assert getStateInitSchema() == null && concreteStateInit_ == null ||
           getStateInitSchema() != null && concreteStateInit_ != null;

    if (getStateInitSchema() != null && concreteStateInit_ != null &&
        containsRefPair(getStateInitSchema(), concreteStateInit_))
    {
      Expr absStInit = zptr.createSchRef(getStateInitSchema(), stateGenParams);
      Expr conStInit = zptr.createSchRef(concreteStateInit_, concreetStateGenParams_);
      Expr retrieveDashRef = zptr.createDashedSchRef(retr, retrieveGenParams_);

      // use RetrieveGenParams as it encompases both AS and CS; create a ConjPara for the VC as its "para"
      loc = getLocation(cState, aState);
      Pred initVC = zptr.createInitialisationVC(rk, absStInit, conStInit, retrieveDashRef);
      addRefVC(vcList, rk, ZRefVCKind.Initialisation, retrieveGenParams_, initVC, cState, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find state initialisations for neither abstract nor concrete state";
      CztLogger.getLogger(getClass()).warning(message);
    }

    // Don't use as variable as the method might change its values
    //ZName aStateFin = getStateFinSchema();
    okay = checkNeedsComplementarySchema(getStateFinSchema(), concreteStateFin_, ZRefVCKind.Finalisation);
    assert getStateFinSchema() == null && concreteStateFin_ == null ||
           getStateFinSchema() != null && concreteStateFin_ != null;

    // if there is any finalisation to do, create the VC for it
    if (getStateFinSchema() != null && concreteStateFin_ != null &&
        containsRefPair(getStateFinSchema(), concreteStateFin_))
    {
      Expr absStFin = zptr.createSchRef(getStateFinSchema(), stateGenParams);
      Expr conStFin = zptr.createSchRef(concreteStateFin_, concreetStateGenParams_);
      Expr retrieveRef = zptr.createSchRef(retr, retrieveGenParams_);
      loc = getLocation(concreteStateFin_, getStateFinSchema(), cState, aState);
      Pred finVC = zptr.createFinalisationVC(rk, absStFin, conStFin, retrieveRef);
      addRefVC(vcList, rk, ZRefVCKind.Finalisation, getRetrieveGenParams(), finVC, cState, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find state finalisations for neither abstract nor concrete state";
      CztLogger.getLogger(getClass()).warning(message);
    }

    okay = checkNeedsComplementarySchema(abstractStateInitIn_, concreteStateInitIn_, ZRefVCKind.InitialisationInput);
    assert abstractStateInitIn_ == null && concreteStateInitIn_ == null ||
           abstractStateInitIn_ != null && concreteStateInitIn_ != null;

    // if got created and we don't have a retrieve for IO, add a default one
    if (okay)
    {
      if (retrieveIn_ == null)
      {
        final String message = "Could not find retrieve input schema. Adding a default one";
        CztLogger.getLogger(getClass()).warning(message);
      }
      if (getStateInitSchema() == null)
      {
        
      }
      if (concreteStateInit_ == null)
      {

      }
    }

    if (retrieveIn_ != null && definitions_.containsKey(retrieveIn_) &&
        abstractStateInitIn_ != null && concreteStateInitIn_ != null &&
        containsRefPair(abstractStateInitIn_, concreteStateInitIn_))
    {
      Expr absInitIn = zptr.createSchRef(abstractStateInitIn_, stateGenParams);
      Expr conInitIn = zptr.createSchRef(concreteStateInitIn_, retrieveInGenParams_);
      Expr retIn =  zptr.createSchRef(retrieveIn_, retrieveInGenParams_);
      
      Pred ioInit = zptr.createInitialisationInputVC(rk, absInitIn, conInitIn, retIn);
      loc = getLocation(concreteStateInitIn_, concreteStateInit_, retrieveIn_, cState);
      addRefVC(vcList, rk, ZRefVCKind.InitialisationInput, retrieveInGenParams_, ioInit, retrieveIn_, loc);
    }
    else
    {
      assert !okay;
      final String message = "Could not find initialisation schemas for neither abstract and concrete inputs";
      CztLogger.getLogger(getClass()).warning(message);
    }

    okay = checkNeedsComplementarySchema(abstractStateFinOut_, concreteStateFinOut_, ZRefVCKind.FinalisationOutput);
    assert abstractStateFinOut_ == null && concreteStateFinOut_ == null ||
           abstractStateFinOut_ != null && concreteStateFinOut_ != null;

    if (okay)
    {
      if (retrieveOut_ == null)
      {
        final String message = "Could not find retrieve input schema. Adding a default one";
        CztLogger.getLogger(getClass()).warning(message);
      }
      if (getStateFinSchema() == null)
      {

      }
      if (concreteStateFin_ == null)
      {

      }
    }

    if (retrieveOut_ != null && definitions_.containsKey(retrieveOut_) &&
        abstractStateFinOut_ != null && concreteStateFinOut_ != null &&
        containsRefPair(abstractStateFinOut_, concreteStateFinOut_))
    {
      Expr absFinOut = zptr.createSchRef(abstractStateFinOut_, stateGenParams);
      Expr conFinOut = zptr.createSchRef(concreteStateFinOut_, retrieveOutGenParams_);
      Expr retOut = zptr.createSchRef(retrieveOut_, retrieveOutGenParams_);

      Pred ioFin  = zptr.createFinalisationOutputVC(rk, absFinOut, conFinOut, retOut);
      loc = getLocation(concreteStateFinOut_, concreteStateFin_, retrieveOut_, cState);
      addRefVC(vcList, rk, ZRefVCKind.FinalisationOutput, retrieveOutGenParams_, ioFin, retrieveOut_, loc);
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
   * @param abs
   * @param con
   * @param vckind
   * @return
   */
  private boolean checkNeedsComplementarySchema(ZName abs, ZName con, ZRefVCKind vckind)
  {
    boolean result = false;
    AxPara axPara;
    if (abs != null && con == null)
    {
      switch (vckind)
      {
        case Initialisation:
          assert concreteStateInit_ == null;
          con = factory_.createZName(ZStateInfo.CSTINIT.toString());
          concreteStateInit_ = con;
          // CSInit == [ CState' | true ]
          axPara = predTransformer_.createSchExpr(concreetStateGenParams_, con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(concreteState_, concreetStateGenParams_)));
          break;
        case InitialisationInput:
          assert concreteStateInitIn_ == null;
          con = factory_.createZName(ZStateInfo.CINITIN.toString());
          concreteStateInitIn_ = con;
          // CInitIn == [ inputs-from-CSInit | true ]
          axPara = predTransformer_.createSchExpr(retrieveInGenParams_, con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, retrieveInGenParams_)));
          break;
        case Finalisation:
          // CSFin == [ CState | true ]
          assert concreteStateFin_ == null;
          con = factory_.createZName(ZStateInfo.CSTFIN.toString());
          concreteStateFin_ = con;
          axPara = predTransformer_.createSchExpr(concreetStateGenParams_, con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createSchRef(concreteState_, concreetStateGenParams_)));
          break;
        case FinalisationOutput:
          assert concreteStateFinOut_ == null;
          con = factory_.createZName(ZStateInfo.CSTINIT.toString());
          concreteStateFinOut_ = con;
          // CFinOut == [ outputs-from-CSInit | true ]
          axPara = predTransformer_.createSchExpr(retrieveOutGenParams_, con,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, retrieveOutGenParams_)));
          break;
        default:
          throw new IllegalArgumentException("invalid ZRefVCKind " + vckind);
      }
      assert con != null;
      addedSigSchemas_.put(con, axPara);
      final String message = "Could not find concrete schema for VC " + vckind.toString() + " generation. Creating a default one as " + con;
      CztLogger.getLogger(getClass()).warning(message);
      result = true;
    }
    else if (con != null && abs == null)
    {
      switch (vckind)
      {
        case Initialisation:
          assert getStateInitSchema() == null;
          abs = factory_.createZName(ZStateInfo.CSTINIT.toString());
          setZStateInitName(abs);
          // ASInit == [ AState' | true ]
          axPara = predTransformer_.createSchExpr(getStateSchemaGenParams(), abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(getStateSchema(), getStateSchemaGenParams())));
          break;
        case InitialisationInput:
          assert abstractStateInitIn_ == null;
          abs = factory_.createZName(ZStateInfo.CINITIN.toString());
          abstractStateInitIn_ = abs;
          // AInitIn == [ inputs-from-ASInit | true ]
          axPara = predTransformer_.createSchExpr(retrieveInGenParams_, abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, retrieveInGenParams_)));
          break;
        case Finalisation:
          // ASFin == [ AState | true ]
          assert getStateFinSchema() == null;
          abs = factory_.createZName(ZStateInfo.CSTFIN.toString());
          setZStateFinName(abs);
          axPara = predTransformer_.createSchExpr(getStateSchemaGenParams(), abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createSchRef(getStateSchema(), getStateSchemaGenParams())));
          break;
        case FinalisationOutput:
          assert abstractStateFinOut_ == null;
          abs = factory_.createZName(ZStateInfo.CSTINIT.toString());
          abstractStateFinOut_ = abs;
          // AFinOut == [ outputs-from-ASInit | true ]
          axPara = predTransformer_.createSchExpr(retrieveOutGenParams_, abs,
                    predTransformer_.createSchemaInclusion(
                      predTransformer_.createDashedSchRef(null, retrieveOutGenParams_)));
          break;
        default:
          throw new IllegalArgumentException("invalid ZRefVCKind " + vckind);
      }
      assert abs != null;
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
    ZName aState  = getStateSchema();
    ZName cState  = getConcreteStateName();
    ZName retr    = getRetrieveName();
    ZName retrIn  = getRetrieveInName();
    ZName retrOut = getRetrieveOutName();
    ZNameList absGenParams = getStateSchemaGenParams();
    ZNameList allGenParams = getRetrieveGenParams();
    assert aState != null && cState != null && retr != null;

    // references
    Expr astateRef = zptr.createSchRef(aState, absGenParams);
    Expr astateDashRef = zptr.createDashedSchRef(aState, absGenParams);
    Expr cstateRef = zptr.createSchRef(cState, concreetStateGenParams_);
    Expr retrieveRef = zptr.createSchRef(retr, retrieveGenParams_);
    Expr retrieveDashRef = zptr.createDashedSchRef(retr, retrieveGenParams_);

    // TODO: for now keep the given states' generic params. Later allow for IO gen params as well
    Expr absOpRef = zptr.createSchRef(absName, absGenParams);
    Expr conOpRef = zptr.createSchRef(conName, concreetStateGenParams_);

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
    Expr conOpSigRef = zptr.createSchRef(conSigName, concreetStateGenParams_);


    // TODO: no IO refinement for now
    Expr retrieveInRef = null;
    Expr retrieveOutRef = null;
    if (retrIn != null)
    {
      if (retrOut == null)
      {
        // TODO: generalise this naming convention? Or use the VC name factory?
        retrOut = factory_.createZName(retrieve_.getWord() + "RIn");
        retrieveOutRef = zptr.createSchRef(retrOut, retrieveOutGenParams_);
      }
      retrieveInRef = zptr.createSchRef(retrIn, retrieveInGenParams_);
    }
    if (retrOut != null)
    {
      if (retrIn == null)
      {
        retrIn = factory_.createZName(retrieve_.getWord() + "ROut");
        retrieveInRef = zptr.createSchRef(retrIn, retrieveOutGenParams_);
      }
      retrieveOutRef = zptr.createSchRef(retrOut, retrieveOutGenParams_);
    }

    LocAnn loc = getLocation(conName, absName);

    Pred fpred = zptr.createFeasibilityVC(rk, absOpSigRef, absOpRef, conOpSigRef, conOpRef, retrieveRef, retrieveInRef);
    addRefVC(vcList, rk, ZRefVCKind.Applicability, allGenParams, fpred, conName, loc);

    Pred cpred = zptr.createCorrectnessVC(rk, astateRef, astateDashRef, absOpRef, cstateRef, conOpRef, retrieveRef, retrieveDashRef, retrieveInRef, retrieveOutRef);
    addRefVC(vcList, rk, ZRefVCKind.Correctness, allGenParams, cpred, conName, loc);
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

  protected void addRefVC(List<VC<Pred>> vcList, ZRefKind rk, ZRefVCKind vcrk,
                          ZNameList genParams, Pred pred, ZName opName, LocAnn loc) throws VCCollectionException
  {
    stepVCCounter();
    ConjPara conjPara = getPredTransformerRef().createExtraVCConjPara(rk, vcrk, genParams, pred, opName, loc);
    VC<Pred> refVC = createVC(getVCCount(), conjPara, VCType.NONE, pred);
    vcList.add(refVC);
  }
}
