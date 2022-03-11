/*
  Copyright (C) 2007 Leo Freitas
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
package net.sourceforge.czt.typecheck.circusconf;

import java.util.List;
import java.util.ListIterator;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelProcess;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.HideProcess;
import net.sourceforge.czt.circus.ast.IndexedProcess;
import net.sourceforge.czt.circus.ast.ParProcess;
import net.sourceforge.czt.circus.ast.ParallelProcess;
import net.sourceforge.czt.circus.ast.ParamProcess;
import net.sourceforge.czt.circus.ast.Process2;
import net.sourceforge.czt.circus.ast.ProcessD;
import net.sourceforge.czt.circus.ast.ProcessIdx;
import net.sourceforge.czt.circus.ast.ProcessIte;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.CallUsage;
import net.sourceforge.czt.circus.ast.RenameProcess;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelProcessVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.CallProcessVisitor;
import net.sourceforge.czt.circus.visitor.HideProcessVisitor;
import net.sourceforge.czt.circus.visitor.IndexedProcessVisitor;
import net.sourceforge.czt.circus.visitor.ParallelProcessVisitor;
import net.sourceforge.czt.circus.visitor.ParamProcessVisitor;
import net.sourceforge.czt.circus.visitor.Process2Visitor;
import net.sourceforge.czt.circus.visitor.ProcessIdxVisitor;
import net.sourceforge.czt.circus.visitor.ProcessIteVisitor;
import net.sourceforge.czt.circus.visitor.RenameProcessVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;

/**
 * This visitor produces a ProocessSignature for each Circus process class.
 * This could be either a ProcessSignature, depending whether we have a 
 * process description or a basic process with 
 * state and actions. This follows the Parser "processDesc" non-terminal
 * production.
 *
 * @author Leo Freitas
 */
public class ProcessChecker extends Checker<CircusCommunicationList>
  implements 
      ParamProcessVisitor<CircusCommunicationList>,      // C.6.3, C.6.6
      IndexedProcessVisitor<CircusCommunicationList>,    // C.6.4, C.6.7
      ZParaListVisitor<CircusCommunicationList>,         // C.7.1, C.7.2      
      BasicProcessVisitor<CircusCommunicationList>,      // C.8.1
      CallProcessVisitor<CircusCommunicationList>,       // C.8.2, C.8.9--C.8.15
      HideProcessVisitor<CircusCommunicationList>,       // C.8.3
      Process2Visitor<CircusCommunicationList>,           
      //SeqActionVisitor,                            C.8.4
      //ExtChoiceActionVisitor,                      C.8.5
      //IntChoiceActionVisitor,                      C.8.6      
      //InterleaveProcessVisitor,                    C.8.7
      ParallelProcessVisitor<CircusCommunicationList>,   // C.8.8
      AlphabetisedParallelProcessVisitor<CircusCommunicationList>, //  C.8.8-2
      RenameProcessVisitor<CircusCommunicationList>,     // C.8.16
      ProcessIteVisitor<CircusCommunicationList>,        // C.8.17--C.8.21-2
      ProcessIdxVisitor<CircusCommunicationList>         // same C.8.17--C.8.21-2 for indexes - no scope for them though      
{

  private ProcessSignature processSig_;

  /** Creates a new instance of ProcessChecker */
  public ProcessChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    setCurrentProcessSignature(null);
  }

  protected ProcessSignature getCurrentProcessSignature()
  {
    checkProcessSignature(null);
    return processSig_;
  }
  
  protected ProcessSignature setCurrentProcessSignature(ProcessSignature sig)
  {
    ProcessSignature old = processSig_;
    processSig_ = sig;
    return old;
  }
  
  protected void checkProcessSignature(Object term)
  {
    assert processSig_ != null : "null process signature whilst visiting " + (term != null ? term.getClass().getSimpleName() : "null");
  }
  
  protected void checkProcessSignatureNotBasic(Object term)
  {
    assert processSig_ != null && !processSig_.isBasicProcessSignature() : (term != null ? term.getClass().getSimpleName() : "null") + " cannot have basic process signature";
  }

  protected List<Object> getChannelSetErrorParams()
  {
    // within the ProcessChecker, it must be for an process use rather than at declaration point.
    List<Object> errorParams = factory().list();
    errorParams.add("process");
    errorParams.add(getCurrentProcessName().toString());
    return errorParams;
    // Avoid this simple version: it gives a read-only array, which is wrong as errorParams will grow with more info from where this is called.
    //return Arrays.asList("process", getCurrentProcessName());
  }

  /**
   * This general method typechecks all parameterised processes. It covers ParamProcess;
   * annd all ProcessIte, and ProcessIdx.
   * It checks the declared parameters (possibly including generic types from 
   * the process) for duplicated names and type mismatches, 
   * putting then into scope. Finally, it typechecks the declaring process with 
   * the parameters in scope adding them to the resulting process signature with 
   * the formal parameters set. For indexed declarations, the variables are not
   * put into the process local scope, as they are not to be referenced.
   * 
   */
  protected CircusCommunicationList typeCheckProcessD(ProcessD term,
    boolean iterated, boolean putDeclsIntoScope)
  {
    checkProcessParaScope(term, null);

    // type check the list of declared parameters - it returns the
    // formal parameters signature already considering generics    
    List<NameTypePair> gParams = typeCheckCircusDeclList(
      term, term.getZDeclList(), iterated /* considerFiniteness */,
      false /* allowQualifiedDecl */, ErrorMessage.INVALID_DECL_IN_PROCESSITE,
      factory().<Object>list(getCurrentProcessName()));

    // put the declared parameters into the action's scope
    typeEnv().enterScope();

    // indexes are not to be put into scope.
    if (putDeclsIntoScope)
    {
      typeEnv().add(gParams);
    }

    // check the inner process now with the parameters in scope
    CircusProcess process = term.getCircusProcess();
    CircusCommunicationList commList = process.accept(processChecker());

    // if nesting is present, raise an error - it isn't allowed 
    //(but only for compound signatures since basic cannot have it anyway
    // unless this is call action, in which case parameters may be present    
    
    ProcessSignature currentSignature = getCurrentProcessSignature();    
    if (!(process instanceof CallProcess) && 
        !currentSignature.isBasicProcessSignature() &&
        !currentSignature.getFormalParamsOrIndexes().getNameTypePair().isEmpty())
    {
      Object[] params = {getCurrentProcessName()};
      error(term, ErrorMessage.NESTED_FORMAL_PARAMS_IN_PROCESS, params);
    }

    // updates the formal parameters signature with gParams
    ProcessSignature oldSignature;
    ProcessSignature paramSignature = factory().createParamProcessSignature(factory().
        createSignature(gParams), factory().createProcessSignatureList(factory().list(currentSignature)),
        (putDeclsIntoScope ? CallUsage.Parameterised : CallUsage.Indexed));        
    paramSignature.setGenFormals(factory().createZNameList(typeEnv().getParameters()));
    //paramSignature.setProcessName(getCurrentProcessName());        
    if (iterated)
    {
      // iterated processes do not have parameters - hence should not be part of signature
      paramSignature.getFormalParamsOrIndexes().getNameTypePair().clear();            
    }
    oldSignature = setCurrentProcessSignature(paramSignature);
    assert oldSignature == currentSignature : "inconsistent signature update for ProcessD " +  term.getClass().getSimpleName();
    
    typeEnv().exitScope();

    return commList;
  }

  protected CircusCommunicationList typeCheckParProcess(ParProcess term,
    List<ChannelSet> channelSets)
  { 
    // within the ProcessChecker, it must be for an process use rather than at declaration point.
    List<Object> errorParams = getChannelSetErrorParams();

    // check the channel sets - do it first so that processSig_ won't be basic
    for (ListIterator<ChannelSet> lit =
      channelSets.listIterator(channelSets.size());
      lit.hasPrevious();)
    {
      ChannelSet cs = lit.previous();
      @SuppressWarnings("unused")
	ChannelSetType cst = typeCheckChannelSet(cs, errorParams);      
      GlobalDefs.addNoDuplicates(0, cs, processSig_.getCircusProcessChannelSets());
    }    

    // typecheck inner processes - do each side latter to allow right settling of (possibly basic) signatures
    CircusCommunicationList commList = visitProcess2(term);

    return commList;
  }

  /**
   * Typechecks all iterated processes. It performs the general protocol for
   * processes with declaring parameters (ProcessD), then make sure the 
   * types within the declarations are finite, and put the declarations into scope
   * @param term
   * @return
   */
  protected CircusCommunicationList typeCheckProcessIte(ProcessIte term)
  {
    // all ProcessIte are typechecked just liked ProcessD
    // - no qualified declaration is allowed - 
    // and types of declarations ought to be finite
    CircusCommunicationList commList = typeCheckProcessD(term,
      true, /* iterated */
      true  /* putDeclsIntoScope */);        
    return commList;
  }

  /**
   * Typechecks all iterated and indexed processes. It performs the general protocol for
   * processes with declaring parameters (ProcessD), then make sure the 
   * types within the declarations are finite, but DO NOT put the declarations into scope
   * @param term
   * @return
   */
  protected CircusCommunicationList typeCheckProcessIdx(ProcessIdx term)
  {
    // all ProcessIte are typechecked just liked ProcessD
    // - no qualified declaration is allowed - 
    // and types of declarations ought to be finite
    CircusCommunicationList commList = typeCheckProcessD(term,
      true,  /* iterated */
      false  /* putDeclsIntoScope */);    
    return commList;
  }

  private enum PSigResolution
  {
    Both, Current, Given, Neither
  }
  ;

  private static final  PSigResolution    
      [][] PSIG_MATRIX = 
      {                          /* given not basic        given basic */
        /* current not basic */  { PSigResolution.Neither, PSigResolution.Given },  
        /* current basic     */  { PSigResolution.Current, PSigResolution.Both } 
      }
  ;
  
  protected void updateCurrentProcessSignature(ProcessSignature processSignature)
  {    
    checkProcessSignature(null);
    ProcessSignature pSig = processSignature;//factory().deepCloneTerm(processSignature);
    PSigResolution pSigResolution = PSIG_MATRIX[processSig_.isBasicProcessSignature() ? 1 : 0][pSig.isBasicProcessSignature() ? 1 : 0];    
    switch(pSigResolution)
    {
      case Both:        
        processSig_.setStateSignature(pSig.getStateSignature());
        processSig_.getBasicProcessLocalZSignatures().addAll(pSig.getBasicProcessLocalZSignatures());
        processSig_.getActionSignatures().addAll(pSig.getActionSignatures());                 
        break;
      case Current:     
        if (processSig_.isEmptyProcessSignature())
        {
          // if empty, just consider the given one
          processSig_.getProcessSignatures().addAll(pSig.getProcessSignatures());        
        }
        else
        {
          // otherwise, clone current and create new processSig_.
          ProcessSignature newPSig = factory().createEmptyProcessSignature();
          //newPSig.setProcessName(processSig_.getProcessName());
          newPSig.setGenFormals(processSig_.getGenFormals());          
          newPSig.getProcessSignatures().add(processSig_);
          GlobalDefs.addAllNoDuplicates(pSig.getProcessSignatures(), newPSig.getProcessSignatures());
          
          setCurrentProcessSignature(newPSig);
        }
        break;
      case Given:
        // do not add repeated bpSig into pSig
        if (!processSig_.getProcessSignatures().contains(pSig)) 
        {
          processSig_.getProcessSignatures().add(pSig);
        }
        break;
      case Neither:        
        for(ProcessSignature ps : pSig.getProcessSignatures())
        {
          updateCurrentProcessSignature(ps);
        }
        GlobalDefs.addAllNoDuplicates(pSig.getCircusProcessChannelSets(), processSig_.getCircusProcessChannelSets());
        // TODO: CHECK: ignore nested formals here, since this is checked at typeCheckProcessD ?        
        break;
    }    
  }
  
  protected void addImplicitChannels(CircusProcess term, CircusCommunicationList commList)
  {
    checkProcessSignatureNotBasic(term);
    assert !processSig_.getFormalParamsOrIndexes().getNameTypePair().isEmpty() 
      : "cannot add implicit channels for indexed process without indexes";
     
    ProcessSignature indexedSignature = processSig_;//factory().deepCloneTerm(processSig_);
    
    // set the process name as current because we need it for getUsedChannels()    
    boolean resetToNull = indexedSignature.getProcessName() == null;
    if (resetToNull)
    {
      indexedSignature.setProcessName(getCurrentProcessName());
    }
    
    // resolve any mutual recursion so that 
    // communication list can be collected fully
    if (needPostCheck())
    {
      postCheck();
      
      // update communication list after post check
      GlobalDefs.addAllNoDuplicates(indexedSignature.getUsedCommunicationsAsList(), commList);
    }
    
    // build the extended NameTypePair information
    List<NameTypePair> indexes = indexedSignature.getFormalParamsOrIndexes().getNameTypePair();      
    String extendedName = "";
    ProdType extendedType = factory().createProdType(factory().<Type2>list());
    for(NameTypePair ntp : indexes)
    {
      extendedName = "\\_" + ntp.getZName().getWord();
      extendedType.getType().add(GlobalDefs.unwrapType(ntp.getType()));
    }
    
    // for each signature of each inner process or action of this indexed process,
    // add implicit channels w.r.t. the indexes type
    for(Signature sig : indexedSignature.getUsedChannels().values())
    {
      for(NameTypePair ntp : sig.getNameTypePair())
      {
        // extend the name
        ZName nameToExtend = ntp.getZName();
        nameToExtend.setWord(nameToExtend.getWord() + extendedName);
        factory().addNameID(nameToExtend);
        
        // extend the type        
        assert (ntp.getType() instanceof ChannelType) : "cannot implicit extend non channel type: " + ntp.getType();
        ChannelType cType = (ChannelType)ntp.getType();
        Type2 typeToExtend = cType.getType();
        if (typeToExtend instanceof ProdType)
        {
          GlobalDefs.prodType(typeToExtend).getType().addAll(0, extendedType.getType());
        }
        else
        {
          ProdType productType = factory().createProdType(
            factory().list(GlobalDefs.unwrapType(typeToExtend)));
          productType.getType().addAll(0, extendedType.getType());
          cType.setType(productType);
          typeToExtend = productType;
        }
        assert GlobalDefs.prodType(typeToExtend).getType().size() > 1 
          : "invalid extended product type for implicit channel - " + typeToExtend;    
        
        // add it to the local scope for this process
        typeEnv().add(ntp);  
      }      
    }
    if (resetToNull)
    {
      indexedSignature.setProcessName(null);
    }
    setCurrentProcessSignature(indexedSignature);
  }

  /**
   * 
   * @param term
   * @return
   * @law C.6.3, C.6.6
   */
  @Override
  public CircusCommunicationList visitParamProcess(ParamProcess term)
  {
    // commands allow qualified declarations    
    // and types of declarations do not need to be finite
    CircusCommunicationList commList = typeCheckProcessD(term,
      false, /* iterated */
      true   /* putDeclsIntoScope */);
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.6.4, C.6.7
   */
  @Override
  public CircusCommunicationList visitIndexedProcess(IndexedProcess term)
  {
    CircusCommunicationList commList = typeCheckProcessD(term,
      false, /* iterated */
      false  /* putDeclsIntoScope */);
    
    // add implicit channels and update communication list
    addImplicitChannels(term, commList);    
    return commList;
  }  
  
  /**
   * 
   * @param term
   * @return
   * @law C.8.1, C.7.1, C.7.2
   */
  public CircusCommunicationList visitZParaList(ZParaList term)
  {   
    checkProcessParaScope(term, null);
    
    // we could have compound basic processes, such as tc327\_intchoice\_bp
    //assert getCurrentBasicProcess() != null : "Cannot check paragraph list outside basic process";
        
    assert basicProcessChecker().getCurrentBasicProcesssignature() == null : "nested basic processes are not allowed";

    // sets the visitor current signature as the preocess signature        
    ProcessSignature bpSig = factory().createEmptyProcessSignature();
    //bpSig.setProcessName(getCurrentProcessName());
    bpSig.setGenFormals(factory().createZNameList(typeEnv().getParameters()));        
    basicProcessChecker().setCurrentBasicProcessSignature(bpSig);
    
    CircusCommunicationList commList = factory().createEmptyCircusCommunicationList();
    
    for (Para para : term)
    {      
      CircusCommunicationList paraCommList = para.accept(basicProcessChecker());
      GlobalDefs.addAllNoDuplicates(paraCommList, commList);
    }

    // for mutually recursive actions.
    if (needPostCheck())
    {
      postCheck();
      
      // update the action communication list for each action within basic process
      //processSig_.getActions()      
    }
    
    // clear the visitor's current signature.
    updateCurrentProcessSignature(basicProcessChecker().getCurrentBasicProcesssignature());
    basicProcessChecker().setCurrentBasicProcessSignature(null);        
        
    // no sig annotation need to be added here.
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.1
   */
  @Override
  public CircusCommunicationList visitBasicProcess(BasicProcess term)
  {
    checkProcessParaScope(term, null);

    // check the paragraph list of a basic process. 
    // this includes the main action, state paragraph,
    // on-the-fly actions, and other usual circus and paragraphs.
    CircusCommunicationList commList = term.getZParaList().accept(processChecker());

    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.2, C.8.9--C.8.15
   */
  @Override
  public CircusCommunicationList visitCallProcess(CallProcess term)
  {
    // NOTE: Most of this code follows the pattern from z.ExprChecker.visitRefExpr.

    RefExpr callExpr = term.getCallExpr();
    Name call = callExpr.getName();

    // check the scope
    checkProcessParaScope(term, call);

    // see if this call has already been type checked
    boolean addedPostChecking = false;
    
    // always check  the expression because of the generic parameters
    Type type = callExpr.accept(exprChecker());    
    //add this call for post checking --- this is CZT's approach
    if (!GlobalDefs.containsObject(paraErrors(), term))
    {
      addTermForPostChecking(term);
      addedPostChecking = true;
    }
     
    //if this is undeclared, create an unknown type with this CallAction
    //i.e., getType(call) may add a UndeclaredAdd to call
    Object undecAnn = call.getAnn(UndeclaredAnn.class);

    //if we are using name IDs, then read the type off the name if it
    //is not in the type environment    
    // TODO: CHECK: ask Tim, this is a known name then?
    if (undecAnn != null && sectTypeEnv().getUseNameIds())
    {
      type = GlobalDefs.getTypeFromAnns(term);
      if (!(type instanceof UnknownType))
      {
        GlobalDefs.removeAnn(call, UndeclaredAnn.class);
        undecAnn = null;
      }
    }

    // if name is unknown, add the call to its list of associated names.
    if (undecAnn != null)
    {
      assert type instanceof UnknownType;
      UnknownType uType = (UnknownType) type;
      uType.setZName(ZUtils.assertZName(call));

      // post checking ?      
      if (!addedPostChecking)
      {
        addTermForPostChecking(term);
        //addAction4PostCheck(getCurrentActionName());
        addedPostChecking = true;
      }   
    }
    
    List<ErrorAnn> callErrors = checkCallProcessConsistency(
      GlobalDefs.unwrapType(type), term, true /* checkProcessScope */);
    if (addedPostChecking)
    { 
      appendCallErrors(call, callErrors);      
    }
    else
    {      
      raiseErrors(term, callErrors);
    }
    
    CircusCommunicationList commList = factory().createEmptyCircusCommunicationList();

    // if action type, then clone the call signature
    if (type instanceof ProcessType)
    {      
      ProcessSignature procSig = GlobalDefs.processType(type).getProcessSignature();
      procSig = factory().deepCloneTerm(procSig);
      procSig.setProcessName(call);
      CircusCommunicationList callCommList = factory().createCircusCommunicationList(procSig.getUsedCommunicationsAsList());
      //callCommList = factory().deepCloneTerm(callCommList);
      GlobalDefs.addAllNoDuplicates(callCommList, commList);      
      updateCurrentProcessSignature(procSig);
    }        
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.3
   */
  @Override
  public CircusCommunicationList visitHideProcess(HideProcess term)
  {
    // check within an process paragraph scope.
    checkProcessParaScope(term, null);

    // typecheck and update channel sets used
    ChannelSet cs = term.getChannelSet();
    @SuppressWarnings("unused")
	ChannelSetType csType = typeCheckChannelSet(cs, getChannelSetErrorParams());
    GlobalDefs.addNoDuplicates(0, cs, processSig_.getCircusProcessChannelSets()); 

    // check the process itself and add signature
    CircusCommunicationList commList = term.getCircusProcess().accept(processChecker());

    checkProcessSignatureNotBasic(term);
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.4, C.8.5, C.8.6, C.8.7 
   */
  @Override
  public CircusCommunicationList visitProcess2(Process2 term)
  {
    // check within an process paragraph scope.
    checkProcessParaScope(term, null);

    // check each side    
    ProcessSignature leftSignature = factory().createEmptyProcessSignature();
    ProcessSignature currentSignature = setCurrentProcessSignature(leftSignature);
    assert currentSignature != null : "current signature is null for binary process " + term;    
    CircusCommunicationList commListL = term.getLeftProcess().accept(processChecker());
    
    ProcessSignature rightSignature = factory().createEmptyProcessSignature();
    ProcessSignature processedLeftSignature = setCurrentProcessSignature(rightSignature);
    assert processedLeftSignature == leftSignature : "inconsistent left signature of binary process " + term;
    CircusCommunicationList commListR = term.getRightProcess().accept(processChecker());
    
    // merge communications
    CircusCommunicationList result = factory().createCircusCommunicationList(commListR);
    GlobalDefs.addAllNoDuplicates(0, commListL, result);    
        
    // update current signature with both sides
    ProcessSignature processedRightSignature = setCurrentProcessSignature(currentSignature);
    assert processedRightSignature == rightSignature : "inconsistent right signature of binary process " + term;
    if (currentSignature.isEmptyProcessSignature())
    {
      // empty signatures are most common for process2, except for hiding and parallelism
      // to avoid merging two basic processes into one, directly update here.
      processSig_.getProcessSignatures().add(processedLeftSignature);
      processSig_.getProcessSignatures().add(processedRightSignature);
    }
    else 
    {
      // otherwise, just follow the usual update protocol.
      updateCurrentProcessSignature(processedLeftSignature);
      updateCurrentProcessSignature(processedRightSignature);
    }
        
    checkProcessSignatureNotBasic(term);
    return result;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.8
   */
  @Override
  public CircusCommunicationList visitParallelProcess(ParallelProcess term)
  {
    CircusCommunicationList commList = typeCheckParProcess(term,
      factory().<ChannelSet>list(term.getChannelSet()));    
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.8-2
   */
  @Override
  public CircusCommunicationList visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    CircusCommunicationList commList = typeCheckParProcess(term,
      factory().<ChannelSet>list(term.getLeftAlpha(), term.getRightAlpha()));    
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.16
   */
  @Override
  public CircusCommunicationList visitRenameProcess(RenameProcess term)
  {
    checkProcessParaScope(term, null);

    // first type check the process - it might add implicitly generic channels to the current process scope.
    CircusCommunicationList commList = term.getCircusProcess().accept(processChecker());
    
    typeCheckRenameListAssignmentPairs(term, commList);
    
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.17--C.8.21-2
   */
  @Override
  public CircusCommunicationList visitProcessIte(ProcessIte term)
  {
    CircusCommunicationList commList = typeCheckProcessIte(term);    
    return commList;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.17--C.8.21-2
   */
  @Override
  public CircusCommunicationList visitProcessIdx(ProcessIdx term)
  {
    CircusCommunicationList commList = typeCheckProcessIdx(term);    
    
    // add implicit channels and update communication list
    addImplicitChannels(term, commList);    
    return commList;
  }
}
