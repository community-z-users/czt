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
package net.sourceforge.czt.typecheck.circus;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelProcess;
import net.sourceforge.czt.circus.ast.AssignmentPairs;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
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
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZNameList;
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
public class ProcessChecker extends Checker<ProcessSignature>
  implements 
      ParamProcessVisitor<ProcessSignature>,      // C.6.3, C.6.6
      IndexedProcessVisitor<ProcessSignature>,    // C.6.4, C.6.7
      ZParaListVisitor<ProcessSignature>,         // C.7.1, C.7.2      
      BasicProcessVisitor<ProcessSignature>,      // C.8.1
      CallProcessVisitor<ProcessSignature>,       // C.8.2, C.8.9--C.8.15
      HideProcessVisitor<ProcessSignature>,       // C.8.3
      Process2Visitor<ProcessSignature>,           
      //SeqActionVisitor,                            C.8.4
      //ExtChoiceActionVisitor,                      C.8.5
      //IntChoiceActionVisitor,                      C.8.6      
      //InterleaveProcessVisitor,                    C.8.7
      ParallelProcessVisitor<ProcessSignature>,   // C.8.8
      AlphabetisedParallelProcessVisitor<ProcessSignature>, //  C.8.8-2
      RenameProcessVisitor<ProcessSignature>,     // C.8.16
      ProcessIteVisitor<ProcessSignature>,        // C.8.17--C.8.21-2
      ProcessIdxVisitor<ProcessSignature>         // same C.8.17--C.8.21-2 for indexes - no scope for them though      
{

  private ProcessSignature processSig_;

  /** Creates a new instance of ProcessChecker */
  public ProcessChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    setCurrentProcessSignature(null);
  }

  protected void setCurrentProcessSignature(ProcessSignature sig)
  {
    processSig_ = sig;
  }

  protected List<Object> getChannelSetErrorParams()
  {
    // within the ProcessChecker, it must be for an process use rather than at declaration point.    
    return Arrays.asList("process", getCurrentProcessName());
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
  protected ProcessSignature typeCheckProcessD(ProcessD term,
    boolean considerFiniteness, boolean putDeclsIntoScope)
  {
    checkProcessParaScope(term, null);

    // type check the list of declared parameters - it returns the
    // formal parameters signature already considering generics
    List<NameTypePair> gParams = typeCheckCircusDeclList(
      term, term.getZDeclList(), considerFiniteness,
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
    ProcessSignature processSignature = process.accept(processChecker());

    // clone the signature
    //ActionSignature actionDSig = (ActionSignature)actionSignature.create(actionSignature.getChildren());
    ProcessSignature processDSig = (ProcessSignature) factory().deepCloneTerm(processSignature);

    // if nesting is present, raise an error - it isn't allowed 
    //(but only for compound signatures since basic cannot have it anyway
    //
    // unless this is call action, in which case parameters may be present
    // !(!actionDSig.getFormalParams().getNameTypePair().isEmpty() => action instanceof CallAction)    
    if (!(process instanceof CallProcess) && 
        !processDSig.isBasicProcessSignature() &&
        !processDSig.getFormalParamsOrIndexes().getNameTypePair().isEmpty())
    {
      Object[] params = {getCurrentProcessName()};
      error(term, ErrorMessage.NESTED_FORMAL_PARAMS_IN_PROCESS, params);
    }

    // updates the formal parameters signature with gParams : join process signatures 
    ProcessSignature result = factory().createParamProcessSignature(factory().
      createSignature(gParams),
      factory().createProcessSignatureList(factory().list(processDSig)),
      (putDeclsIntoScope ? CallUsage.Parameterised : CallUsage.Indexed));

    typeEnv().exitScope();

    return result;
  }

  protected ProcessSignature typeCheckParProcess(ParProcess term,
    List<ChannelSet> channelSets)
  {
    // typecheck inner processes
    ProcessSignature processSignature = visitProcess2(term);

    // clone signature and update name sets used - L first; R next
    // i.e., add the last one first at the head then the next, gives this order
    ProcessSignature processDSig = (ProcessSignature) factory().deepCloneTerm(processSignature);

    // within the ProcessChecker, it must be for an process use rather than at declaration point.
    List<Object> errorParams = getChannelSetErrorParams();

    // check the channel sets
    for (ListIterator<ChannelSet> lit =
      channelSets.listIterator(channelSets.size());
      lit.hasPrevious();)
    {
      ChannelSet cs = lit.previous();
      ChannelSetType cst = typeCheckChannelSet(cs, errorParams);
      processDSig.getCircusProcessChannelSets().add(0, cs);
    }

    return processDSig;
  }

  /**
   * Typechecks all iterated processes. It performs the general protocol for
   * processes with declaring parameters (ProcessD), then make sure the 
   * types within the declarations are finite, and put the declarations into scope
   * @param term
   * @return
   */
  protected ProcessSignature typeCheckProcessIte(ProcessIte term)
  {
    // all ProcessIte are typechecked just liked ProcessD
    // - no qualified declaration is allowed - 
    // and types of declarations ought to be finite
    ProcessSignature processSignature = typeCheckProcessD(term,
      true, /* considerFiniteness */
      true /* putDeclsIntoScope */);
    
    // iterated processes do not have parameters
    processSignature.getFormalParamsOrIndexes().getNameTypePair().clear();
    return processSignature;
  }

  /**
   * Typechecks all iterated and indexed processes. It performs the general protocol for
   * processes with declaring parameters (ProcessD), then make sure the 
   * types within the declarations are finite, but DO NOT put the declarations into scope
   * @param term
   * @return
   */
  protected ProcessSignature typeCheckProcessIdx(ProcessIte term)
  {
    // all ProcessIte are typechecked just liked ProcessD
    // - no qualified declaration is allowed - 
    // and types of declarations ought to be finite
    ProcessSignature processSignature = typeCheckProcessD(term,
      true, /* considerFiniteness */
      false /* putDeclsIntoScope */);
    return processSignature;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.6.3, C.6.6
   */
  @Override
  public ProcessSignature visitParamProcess(ParamProcess term)
  {
    // commands allow qualified declarations    
    // and types of declarations do not need to be finite
    ProcessSignature processDSig = typeCheckProcessD(term,
      false, /* considerFiniteness */
      true /* putDeclsIntoScope */);

    addProcessSignatureAnn(term, processDSig);
    return processDSig;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.6.4, C.6.7
   */
  @Override
  public ProcessSignature visitIndexedProcess(IndexedProcess term)
  {
    ProcessSignature processDSig = typeCheckProcessD(term,
      true, /* considerFiniteness */
      false /* putDeclsIntoScope */);

     // extrai os canais implicitos a partir dos canais usados pelo processo
//    List<NameTypePair> usedChans = localCircTypeEnv().getUsedChans();
//    List<NameTypePair> implicitChans = extractImplicitChans(allPairs, usedChans);
//    //
    
    
    addProcessSignatureAnn(term, processDSig);
    return processDSig;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.1, C.7.1, C.7.2
   */
  public ProcessSignature visitZParaList(ZParaList term)
  {
    // just to double check.
    checkProcessParaScope(term, null);    
    
    // we could have compound basic processes, such as tc327\_intchoice\_bp
    //assert getCurrentBasicProcess() != null : "Cannot check paragraph list outside basic process";
    
    assert basicProcessChecker().getCurrentBasicProcesssignature() == null : "nested basic processes are not allowed";

    boolean basicProcessFormatInv = true;

    // sets the visitor current signature as a fresh signature.
    ProcessSignature result = factory().createEmptyProcessSignature();
    basicProcessChecker().setCurrentBasicProcessSignature(result);

    for (Para para : term)
    {
      // Leave this assertion out. If not processed, the checker will get it anyway.
      //assert CircusUtils.isCircusInnerProcessPara(para) || 
      //       GlobalDefs.isIgnorePara(para): 
      //  "invalid process paragraph for " + getCurrentProcessName();

      // check and fill the basic process signature
      Signature paraSig = para.accept(basicProcessChecker());
    }

    // TODO: CHECK THIS WORKS checks mutually recursive calls.
    // Manuela: the Circus type rules do not treat this.
    //postActionCallCheck();

    // for mutually recursive actions.
    if (needPostCheck())
    {
      postCheck();
    }
    // clear the visitor's current signature.
    result = basicProcessChecker().setCurrentBasicProcessSignature(null);

    // no sig annotation need to be added here.
    return result;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.1
   */
  @Override
  public ProcessSignature visitBasicProcess(BasicProcess term)
  {
    checkProcessParaScope(term, null);

    // check the paragraph list of a basic process. 
    // this includes the main action, state paragraph,
    // on-the-fly actions, and other usual circus and paragraphs.
    ProcessSignature processSignature = term.getZParaList().accept(processChecker());

    //procSignature.setParamOrIndexes(null); <- ParamProcess
    //procSignature.setGenFormals(null);     <- ProcessPara
    //procSignature.setProcessName(null);    <- ProcessPara+addProcSignature
    //procSignature.setStateUpdate(null);    <- ??

    // adds the signature and the current process name 
    addProcessSignatureAnn(term, processSignature);

    return processSignature;

  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.2, C.8.9--C.8.15
   */
  @Override
  public ProcessSignature visitCallProcess(CallProcess term)
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
    //Type type = getType2FromAnns(callExpr);
    //if (type instanceof UnknownType)
    //{ 
      // if not, try the environments 
      //type = getGlobalType(call);      
      //if (type instanceof UnknownType)
      //{
        //add this call for post checking --- this is CZT's approach
        if (!GlobalDefs.containsObject(paraErrors(), term))
        {
          paraErrors().add(term);
          addedPostChecking = true;
        }
        // finally, try instantiating generics for process name
        //type = callExpr.accept(exprChecker());// getGlobalType(call);
      //}
   // }
    
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
        paraErrors().add(term);
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

    // calls have the signature of its type or empty if invalid.        
    // yet, the result signature is always empty, so that it does not 
    // contaminate outer signatures being formed.
    ProcessSignature resultSignature = factory().createEmptyProcessSignature();
    ProcessSignature processSignature = factory().createEmptyProcessSignature();

    // if action type, then clone the call signature
    if (type instanceof ProcessType)
    {
      processSignature = factory().deepCloneTerm(GlobalDefs.processType(type).getProcessSignature());
    }    
    
    // update the term action signature as one calculated 
    addProcessSignatureAnn(term, processSignature);    
    resultSignature.setProcessName(getCurrentProcessName());
    
    return resultSignature;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.3
   */
  @Override
  public ProcessSignature visitHideProcess(HideProcess term)
  {
    // check within an process paragraph scope.
    checkProcessParaScope(term, null);

    ChannelSet cs = term.getChannelSet();
    ChannelSetType csType = typeCheckChannelSet(cs, getChannelSetErrorParams());

    // check the process itself and add signature
    ProcessSignature processSignature = term.getCircusProcess().accept(processChecker());

    // clone signature and update name sets used
    ProcessSignature processDSig = (ProcessSignature) factory().deepCloneTerm(processSignature);
    processDSig.getCircusProcessChannelSets().add(0, cs);

    // add signature to the term
    addProcessSignatureAnn(term, processDSig);

    return processDSig;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.4, C.8.5, C.8.6, C.8.7 
   */
  @Override
  public ProcessSignature visitProcess2(Process2 term)
  {
    // check within an process paragraph scope.
    checkProcessParaScope(term, null);

    // check each side
    ProcessSignature processSigL = term.getLeftProcess().accept(processChecker());
    ProcessSignature processSigR = term.getRightProcess().accept(processChecker());

    // join the signatures, if possible (i.e. parsed specs shall always be).    
    ProcessSignature result = joinProcessSignature(term, processSigL,
      processSigR);

    // annotate the term with given signature.
    addProcessSignatureAnn(term, result);

    return result;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.8
   */
  @Override
  public ProcessSignature visitParallelProcess(ParallelProcess term)
  {
    ProcessSignature processDSig = typeCheckParProcess(term,
      factory().<ChannelSet>list(term.getChannelSet()));
    addProcessSignatureAnn(term, processDSig);
    return processDSig;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.8-2
   */
  @Override
  public ProcessSignature visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    ProcessSignature processDSig = typeCheckParProcess(term,
      factory().<ChannelSet>list(term.getLeftAlpha(), term.getRightAlpha()));
    addProcessSignatureAnn(term, processDSig);
    return processDSig;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.16
   */
  @Override
  public ProcessSignature visitRenameProcess(RenameProcess term)
  {
    checkProcessParaScope(term, null);

    // first type check the process - it might add implicitly generic channels to the current process scope.
    ProcessSignature processSignature = term.getCircusProcess().accept(processChecker());
    
    // the parser enforces              #ln1 = #ln2
    AssignmentPairs apairs = term.getAssignmentPairs();
    ZNameList lhs = apairs.getZLHS();
    ZExprList rhs = apairs.getZRHS();

    // check for duplicate names and their local scope    
    List<NameTypePair> channelNames = factory().list();

    // check no duplicate names in the renaming list
    checkForDuplicateNames(lhs, term);

    // check the names in the rename list are channel names
    int i = 1;
    for (Name name : lhs)
    {
      // get the type - globally
      Type type = getGlobalType(name);
      if (type instanceof ChannelType)
      {
        channelNames.add(factory().createNameTypePair(name, type));
      }
      else
      {
        Object[] params = {
          getCurrentProcessName(),
          name, i, type
        };
        error(term, ErrorMessage.IS_NOT_CHANNEL_NAME_IN_PROCESS_RENAMING, params);
      }
      i++;
    }

    // their sizes is enforced by the parser, by double check here
    // for the case of manually created assignments
    if (lhs.size() != rhs.size())
    {
      Object[] params = {
        getCurrentProcessName(),
        "process renaming",
        lhs.size(), rhs.size()
      };
      error(term, ErrorMessage.UNBALANCED_ASSIGNMENT_PAIRS, params);
    }
    else
    {
      i = 1;
      Iterator<Expr> itExpr = rhs.iterator();
      for (NameTypePair ntp : channelNames)
      {
        // get the values
        assert itExpr.hasNext();

        Expr expr = itExpr.next();
        Type2 expected = GlobalDefs.unwrapType(ntp.getType());
        Type2 found = expr.accept(exprChecker());

        if (!unify(found, expected).equals(UResult.SUCC))
        {
          Object[] params = {
            getCurrentProcessName(),
            ntp.getName(), i, expected, found
          };
          error(term, ErrorMessage.PROCESS_RENAMING_LIST_DONT_UNIFY, params);
        }
        i++;
      }
    }
    
    // TODO: used channels/communications must change deep down into all actions! Oh my god!
    warningManager().warn("Process signature for renaming process still requires update on all used communications." +
      "\n\tProcess...: {0}", getCurrentProcessName());

    addProcessSignatureAnn(term, processSignature);
    return processSignature;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.17--C.8.21-2
   */
  @Override
  public ProcessSignature visitProcessIte(ProcessIte term)
  {
    ProcessSignature processDSig = typeCheckProcessIte(term);
    addProcessSignatureAnn(term, processDSig);
    return processDSig;
  }

  /**
   * 
   * @param term
   * @return
   * @law C.8.17--C.8.21-2
   */
  @Override
  public ProcessSignature visitProcessIdx(ProcessIdx term)
  {
    ProcessSignature processDSig = typeCheckProcessIdx(term);
    addProcessSignatureAnn(term, processDSig);
    return processDSig;
  }

//  private List<NameTypePair> extractImplicitChans(List<NameTypePair> decls, List<NameTypePair> usedChans) {
//    List<NameTypePair> result = new ArrayList<NameTypePair>();
//    
//    for(NameTypePair chan : usedChans) {
//      ZDeclName chanName = chan.getZDeclName();
//      Type chanType = chan.getType();
//      String newName = chanName.getWord();
//      List<Type2> newType = new ArrayList<Type2>();
//      for(NameTypePair decl : decls) {
//        newName = newName + "\\_" + decl.getZDeclName().getWord();
//        // TODO: Check why not unwrapType here
//        // newType.add(decl.getType());
//        newType.add(unwrapType(decl.getType()));
//      }
//      
//      if(chanType instanceof GivenType) {
//        ZDeclName name = ((GivenType)chanType).getName();
//        if(!(name.getWord().equals("Synch"))) {
//          newType.add((GivenType)chanType);
//        }
//      } else {
//        // TODO: Check why not unwrapType here
//        // newType.add(chanType);
//        newType.add(unwrapType(chanType));
//      }
//
//      ZDeclName newChanName = factory().createZDeclName(newName, null, null);
//      ProdType newChanType = factory().createProdType(newType);
//      NameTypePair pair = factory().createNameTypePair(newChanName, newChanType);
//
//      if(!result.contains(pair)) {
//        result.add(pair);
//      }
//      
//      if(isGenericChannel(chanName)) {
//        circusTypeEnv().addUsedChannels(true, newChanName);
//      }
//    }
//    return result;
//  }//
//
//  private List axParaSchemaToSchExpr(AxPara axp) {
//    ConstDecl cdecl = (ConstDecl)axp.getSchText().getDecl().get(0);
//    List result = list();
//    result.add(cdecl.getDeclName());
//    result.add((SchExpr)cdecl.getExpr());
//    return result;
////    return (SchExpr)cdecl.getExpr();
//  }
//*/
}
