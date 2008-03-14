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
 * @author Manuela Xavier
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
    ProcessSignature processSignature = term.getCircusProcess().accept(processChecker());

    // clone the signature
    //ActionSignature actionDSig = (ActionSignature)actionSignature.create(actionSignature.getChildren());
    ProcessSignature processDSig = (ProcessSignature) factory().shallowCloneTerm(processSignature);

    // if nesting is present, raise an error - it isn't allowed (but only for compound signatures since basic cannot have it anyway
    if (!processDSig.isBasicProcessSignature() &&
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
    ProcessSignature processDSig = (ProcessSignature) factory().shallowCloneTerm(processSignature);

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

    // retrieve the process type
    Type type = callExpr.accept(exprChecker());// getGlobalType(call);

    boolean addedPostChecking = false;
    //add this reference for post checking --- this is CZT's approach
    if (!GlobalDefs.containsObject(paraErrors(), term))
    {
      // TODO: double check on this as manuela's solution is different from CZT's'
      //       in hers, this is only added within a particular case when the 
      //       action type is unknown and the current action name is different from 
      //       the one being called.
      if (!ZUtils.namesEqual(getCurrentProcessName(), call))
      {
        paraErrors().add(term);
        //addAction4PostCheck(getCurrentActionName());
        addedPostChecking = true; // see this flag below.
      }
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
        paraErrors().add(term);
        //addAction4PostCheck(getCurrentActionName());
        addedPostChecking = true;
      }
    //else  TODO: CHECK this part in manuelas code
    //{
    //  // tratamento especial para o caso de chamada recursiva
    //  List<NameTypePair> params = localCircTypeEnv().getActionInfo(actionDecl).getParams();
    //  // chama um mtodo auxiliar que ir verificar se a chamada est correta
    //  checkCallAction(term, params);
    //}
    }
    
    List<ErrorAnn> callErrors = checkCallProcessConsistency(
      GlobalDefs.unwrapType(type), term, true /* checkProcessScope */);
    raiseErrors(term, callErrors);

    // calls have the signature of its type or empty if invalid.    
    ProcessSignature processSignature = factory().createEmptyProcessSignature();

    // if action type, then clone the call signature
    if (type instanceof ProcessType)
    {
      processSignature = factory().shallowCloneTerm(GlobalDefs.processType(type).getProcessSignature());
    }
    addProcessSignatureAnn(term, processSignature);

    return processSignature;
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
    ProcessSignature processDSig = (ProcessSignature) factory().shallowCloneTerm(processSignature);
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

    ProcessSignature processSignature = term.getCircusProcess().accept(processChecker());

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
//  
//  //ok - verificado em 15/09/2005 s 19:03
//  public ProcessSignature visitProcess2(Process2 term)
//  {
//    ProcessSignature procSigL = term.getLeftProc().accept(processChecker());
//    ProcessSignature procSigR = term.getRightProc().accept(processChecker());    
//    ProcessSignature result = joinProcessSignature(procSigL, procSigR);
//    addProcessSignatureAnn(term, result);
//    return result;
//  }
//
//  // Parameterised process 
//  
//  public ProcessSignature visitParamProcess(ParamProcess term)
//  {    
//    // ParamProcess ::= Declaration @ Process
//    DeclList decls = term.getDeclList();
//    CircusProcess process = term.getCircusProcess();
//    
//    declareFormalParams(decls);
//    
//    // check there are no non-unifiable duplicates within the list of Z names.
//    checkForDuplicateNames(declPairs, ErrorMessage.DUPLICATE_FORMALPARAM_IN_PROCESS, "parameterised");    
//        
//    typeEnv().enterScope();
//
//    typeEnv().add(declPairs);    
//    
//    Signature paramSig = factory().createSignature(declPairs);
//    ProcessSignature procSig = process.accept(processChecker());        
//    progSig.setParamsOrIndexes(paramsSig);    
//    typeEnv().exitScope();
//    
//    addProcessSignatureAnn(term, procSig);
//    
//    return procSig;
//  }  
//
//  // ParamProcess ::= Declaration \odot Process
//  //ok - verificado em 15/09/2005 s 19:05
//  public ProcessSignature visitIndexedProcess(IndexedProcess term)
//  {
//    DeclList decls = term.getZDeclList();        
//    CircusProcess proc = term.getCircusProcess();
//    
//    declareFormalParams(decls);
//    
//    // check there are no non-unifiable duplicates within the list of Z names.
//    checkForDuplicateNames(declPairs, ErrorMessage.DUPLICATE_FORMALPARAM_IN_PROCESS, "indexed");    
//    
///* TODO:
// *    
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    List<Object> paramsError = new ArrayList<Object>();
//    paramsError.add(assertZDeclName(currentProcess()).getWord());
//
//    // novo escopo devido aos canais implicitos
//    localCircTypeEnv().enterScope();
//    
//    for(Decl d : zdl){
//      if (!(d instanceof VarDecl))
//          throw new UnsupportedOperationException("Indexed processes accept only VarDecl!");
//      VarDecl decl = (VarDecl)d;
//      List<NameTypePair> pairs = decl.accept(declChecker());
//      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_INDEX_IN_PROCESS, paramsError);
//    }
//
//    ProcessInfo procInfo = getProcessInfo(currentProcess());
//    procInfo.setKindOfProcess(KindOfProcess.INDEX);
//    procInfo.setParamsOrIndexes(allPairs);
//    
//    ProcessSignature procSignature = proc.accept(processChecker());
//    ProcessSignature signature = cloneProcessSignature(procSignature);
//    Signature sig = factory().createSignature(allPairs);
//    signature.setParamsOrIndexes(sig);
//
//    // extrai os canais implicitos a partir dos canais usados pelo processo
//    List<NameTypePair> usedChans = localCircTypeEnv().getUsedChans();
//    List<NameTypePair> implicitChans = extractImplicitChans(allPairs, usedChans);
//    //
//    
//    localCircTypeEnv().exitScope();
//
//    // adiciona os canais usados...
//    localCircTypeEnv().addUsedChans(implicitChans);
//    //
// 
// *
// */   
//    addProcessSignatureAnn(term, signature);
//        
//    return signature;
//  }  
//   
//  // Process ::= N
//  // Process ::= N(Expression+)
//  // Process ::= N[Expression+]
//  // Process ::= N \lfloor Expression+ \rfloor
//  // Process ::= (Declaration @ Process)(Expression+)
//  // Process ::= (Declaration \odot Process) \lfloor Expression+ \rfloor
//  // Process ::= (\mu N @ Declaration @ Process)(Expression+)
//  // Process ::= (\mu N @ Declaration \odot Process) \lfloor Expression+ \rfloor
//  //ok - verificado em 15/09/2005 s 19:18
//  public ProcessSignature visitCallProcess(CallProcess term)
//  {
//
//    ProcessSignature procSignature = factory().createProcessSignature();
//    RefName procRef = term.getRefName();
//    ZDeclName procDecl = factory().createZDeclName(assertZRefName(procRef));
//    
//    String nameRefProc = procDecl.getWord();
//    if(nameRefProc.startsWith("$$implicitProcess_")) {
//      // pegar da lista de processos implicitos, fazer a verificao e incluir no
//      //SectTypeEnv!!
//      List<ProcessPara> implicitProcs = (List<ProcessPara>)onTheFlyProcesses();
//      for(ProcessPara implicitProc : implicitProcs) {
//        if(nameRefProc.equals(assertZDeclName(implicitProc.getDeclName()).getWord())) {
//          Signature implicitProcSig = implicitProc.accept(paraChecker());
//          // a assinatura de um processo sempre ter� apenas um par
//          NameTypePair pair = (NameTypePair)implicitProcSig.getNameTypePair().get(0);
//          //if the name already exists globally, raise an error
//          if (sectTypeEnv().add(pair.getZDeclName(), pair.getType()) != null) {
//            Object [] params = {pair.getDeclName()};
//            error(pair.getDeclName(), ErrorMessage.REDECLARED_GLOBAL_NAME, params);
//          }
//        }
//      }
//    }
//    
//    // verifica se uma chamada a um processo mu
//    if(isMuProcess(procDecl)) {         
//      ZExprList zActuals = term.getActuals() == null ? null : assertZExprList(term.getActuals());      
//      if(zActuals != null && !zActuals.isEmpty()) {
//        Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//        error(term, ErrorMessage.MU_PROC_CALL_ERROR, params);
//      }
//    }// caso n�o seja uma chamada ao processo mu
//    else {
//      Type typeRefName = (Type)sectTypeEnv().getType(assertZRefName(procRef));
//
//      if(!(typeRefName instanceof UnknownType)) {
//
//        if(!isProcess(procDecl)) {
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), assertZDeclName(procDecl).getWord()};
//          error(term, ErrorMessage.IS_NOT_PROCESS_NAME, params);
//        } else {
//          ProcessType procType = (ProcessType)typeRefName;
//          procSignature = procType.getProcessSignature();
//          // adiciona os canais usados...
//          List<NameTypePair> usedChans = getUsedChannels(procDecl);
//          localCircTypeEnv().addUsedChans(usedChans);
//          //
//
//          List<NameTypePair> paramsOrIndexes = null;
//          if(procSignature.getParamsOrIndexes() != null) {
//            paramsOrIndexes = procSignature.getParamsOrIndexes().getNameTypePair();
//          }
//          // chama um m�todo auxiliar que ir� verificar se a chamada est� correta
//          checkCallProcess(term, paramsOrIndexes);
//        }
//      } 
//      else {
//        if(!(procDecl.equals(currentProcess()))){
////          Object [] params = {currentProcess().getWord(), procDecl.getWord()};
////          error(term, ErrorMessage.IS_NOT_PROCESS_NAME, params);
//          if (!containsObject(paraErrors(), term)) {
//            paraErrors().add(term);
//          }
//        }
//        else {
//          // tratamento especial para o caso de chamada recursiva          
//          List<NameTypePair> paramsOrIndexes = getProcessInfo(procDecl).getParamsOrIndexes();
//          // chama um m�todo auxiliar que ir� verificar se a chamada est� correta
//          checkCallProcess(term, paramsOrIndexes);
//        }
//      }
//    }
//    
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//  
//  
//  // Process ::= \Extchoice Declaration @ Process
//  // Process ::= \Intchoice Declaration @ Process
//  // Process ::= \Semi Declaration @ Process  
//  //ok - verificado em 15/09/2005 �s 19:21
//  public ProcessSignature visitProcessIte(ProcessIte term)
//  {
//    ZDeclList decs = term.getZDeclList();
//    CircusProcess proc = term.getCircusProcess();
//
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    List<Object> paramsError = new ArrayList<Object>();
//    paramsError.add(assertZDeclName(currentProcess()).getWord());
//
//    for(Decl d : decs) {
//        if (!(d instanceof VarDecl))
//          throw new UnsupportedOperationException("Iterated processes accept only VarDecl!");
//       VarDecl dec = (VarDecl)d;
//      boolean declOK = false;
//      if(dec.getExpr() instanceof SetExpr) {
//        declOK = true;
//      }
//      else if(dec.getExpr() instanceof ApplExpr) {
//        ApplExpr applExpr = (ApplExpr)dec.getExpr();
//        if(applExpr.getLeftExpr() instanceof RefExpr) {
//          if(assertZRefName(((RefExpr)applExpr.getLeftExpr()).getRefName()).getWord().equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK)) {
//            declOK = true;
//          }
//        }
//      }
//      List<NameTypePair> pairs = dec.accept(declChecker());
//      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_VAR_IN_PROCESS_ITE, paramsError);
//      if(!declOK) {
//        Object [] params = {assertZDeclName(currentProcess()).getWord()};
//        error(term, ErrorMessage.INFINITY_VALUES_IN_PROCESS_ITE, params);
//        break;
//      }
//    }
//
//    typeEnv().enterScope();
//
//    typeEnv().add(allPairs);
//    ProcessSignature procSig = proc.accept(processChecker());
//    ProcessSignature procSignature = cloneProcessSignature(procSig);
//    Signature sig = factory().createSignature(allPairs);
//    procSignature.setParamsOrIndexes(sig);
//    
//    typeEnv().exitScope();
//    
//    // TODO: Check: added from the other visitors. It is to have the same effect.
//    addProcessAnn(term, procSignature);
//
//    return procSignature;
//  }
//
//  // Process ::= \Parallel Declaration @ |[CSExpression]| Process
//  //ok - verificado em 15/09/2005 �s 19:27
//  public ProcessSignature visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//    ProcessSignature procSignature = visitProcessIte(term);
//    // TODO: Check: already added at visitProcessIte(term).
//    //addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//
//  // Process ::= \Interleave Declaration @ Process
//  //ok - verificado em 15/09/2005 �s 19:28
////  public Object visitInterleaveProcessIte(InterleaveProcessIte term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcessIte(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  // Process ::= |[CSExpression]| Declaration @ Process
//  //ok - verificado em 15/09/2005 �s 19:28
//  public ProcessSignature visitParallelProcessIte(ParallelProcessIte term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    ProcessSignature procSignature = visitProcessIte(term);
//    // TODO: Check: already added at visitProcessIte(term).
//    //addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//  
//  //n�o existe mais
////  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  //n�o existe mais
////  public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  //n�o existe mais
//  public ProcessSignature visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    ProcessSignature procSignature = visitProcessIte(term);
//    // TODO: Check: already added at visitProcessIte(term).
//    //addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//
//  //n�o existe mais
////  public Object visitParProcessIdx(ParProcessIdx term)
////  {
////    return visitProcessIdx(term);
////  }
////  
//  //n�o existe mais
////  public Object visitSeqProcessIdx(SeqProcessIdx term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  //n�o existe mais
//  public ProcessSignature visitParallelProcessIdx(ParallelProcessIdx term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    ProcessSignature procSignature = visitProcessIte(term);
//    // TODO: Check: already added at visitProcessIte(term).
//    //addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//
//  //n�o existe mais
////  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  // Process ::= \mu N @ Process
//  // Process ::= \mu N @ ParamProcess
//  //ok - verificado em 15/09/2005 �s 19:31
//  public ProcessSignature visitMuProcess(MuProcess term)
//  {
//    DeclName name = term.getDeclName();
//    CircusProcess proc = term.getCircusProcess();
//
//    addMuProcess(name);    
//    ProcessSignature signature = proc.accept(processChecker());
//    removeMuProcess(name);
//    
//    addProcessAnn(term, signature);
//    
//    return signature;
//  }
//  
//  // Process ::= Communication -> Process
//  //ok - verificado em 15/09/2005 �s 19:32
//  public ProcessSignature visitPrefixingProcess(PrefixingProcess term)
//  {
//    RefName chanName = term.getCommunication().getChanName();
//    CircusProcess proc = term.getCircusProcess();
//    
//    List<NameTypePair> inputVars = term.getCommunication().accept(commChecker());
//
//    typeEnv().enterScope();
//
//    // ADICIONAR NO AMBIENTE AS VARIA��ES DAS VARI�VEIS DECLARADAS
////    typeEnv().add(inputVars);
//    addVars(inputVars);
//
//    ProcessSignature procSig = proc.accept(processChecker());
//
//    typeEnv().exitScope();
//
//    addProcessAnn(term, procSig);    
//    
//    return procSig;
//  }
//
//  // Process ::= Predicate & Process
//  //ok - verificado em 15/09/2005 �s 19:36
//  public ProcessSignature visitGuardedProcess(GuardedProcess term)
//  {
//    term.getPred().accept(predChecker());
//    ProcessSignature signature = term.getCircusProcess().accept(processChecker());
//    addProcessAnn(term, signature);
//    
//    return signature;
//  }
//
//  // Process ::= Process \ CSExpression
//  //ok - verificado em 15/09/2005 �s 19:36
//  public ProcessSignature visitHideProcess(HideProcess term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    ProcessSignature signature = term.getCircusProcess().accept(processChecker());
//    addProcessAnn(term,  signature);
//    
//    return signature;
//  }
//  
//  // Process ::= Process[N+ := N+]
//  //ok - verificado em 15/09/2005 �s 19:38
//  public ProcessSignature visitRenameProcess(RenameProcess term)
//  {
//    ProcessSignature procSignature = term.getCircusProcess().accept(processChecker());
//    ZRenameList zrl = term.getZRenameList();    
//    int i = 0;
//    for(NewOldPair nop : zrl) {
//        ZDeclName oldName = factory().createZDeclName(nop.getZRefName().getWord(), null, null);
//        ZDeclName newName = factory().createZDeclName(nop.getZDeclName().getWord(), null, null);
//        if(!isChannel(oldName) || !isChannel(newName)) {
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), 
//                  assertZDeclName(procSignature.getProcessName()).getWord()};
//          error(term, ErrorMessage.NAMES_ARE_NOT_CHANNELS_IN_PROC_RENAME, params);
//          break;
//        } else {
//          Type oldType = getChannelType(oldName);
//          Type newType = getChannelType(newName);
//          Type2 expectedU = unwrapType(oldType);
//          Type2 foundU = unwrapType(newType);
//          if (unify(foundU, expectedU) != SUCC) {
//            Object [] params = {expectedU, foundU, i+1, assertZDeclName(procSignature.getProcessName()).getWord()};
//            error(term, ErrorMessage.PROC_RENAME_NOT_UNIFY, params);
//            break;
//          }   
//          // adiciona os canais usados...
//          List<NameTypePair> usedChans = new ArrayList<NameTypePair>();
//          NameTypePair oldC = factory().createNameTypePair(oldName, oldType);
//          usedChans.add(oldC);
//          NameTypePair newC = factory().createNameTypePair(newName, newType);
//          usedChans.add(newC);
//          localCircTypeEnv().addUsedChans(usedChans);                   
//        }
//        i++;
//    }
//    addProcessAnn(term, procSignature);    
//    return procSignature;
//    
//    /*
//    ProcessSignature procSignature = term.getCircusProcess().accept(processChecker());
//    List<RefName> oldNames = (List<RefName>)term.getOldNames();
//    List<RefName> newNames = (List<RefName>)term.getNewNames();
//    
//    if(oldNames.size() == newNames.size()) {
//      int i = 0;
//      for(RefName oldChan : (List<RefName>)oldNames) {
//        DeclName oldName = factory().createDeclName(oldChan.getWord(), null, null);
//        DeclName newName = factory().createDeclName(newNames.get(i).getWord(), null, null);
//        if(!isChannel(oldName.getWord()) || !isChannel(newName.getWord())) {
//          Object [] params = {currentProcess().getWord(), procSignature.getProcessName().getWord()};
//          error(term, ErrorMessage.NAMES_ARE_NOT_CHANNELS_IN_PROC_RENAME, params);
//          break;
//        } else {
//          Type oldType = getChannelType(oldName.getWord());
//          Type newType = getChannelType(newName.getWord());
//          Type2 expectedU = unwrapType(oldType);
//          Type2 foundU = unwrapType(newType);
//          if (unify(foundU, expectedU) != SUCC) {
//            Object [] params = {expectedU, foundU, i+1, procSignature.getProcessName().getWord()};
//            error(term, ErrorMessage.PROC_RENAME_NOT_UNIFY, params);
//            break;
//          }   
//          // adiciona os canais usados...
//          List<NameTypePair> usedChans = list();
//          NameTypePair oldC = factory().createNameTypePair(oldName, oldType);
//          usedChans.add(oldC);
//          NameTypePair newC = factory().createNameTypePair(newName, newType);
//          usedChans.add(newC);
//          localCircTypeEnv().addUsedChans(usedChans);
//          //
//          i++;
//        }
//      }
//    } else {
//      Object [] params = {oldNames.size(), newNames.size(), procSignature.getProcessName().getWord()};
//      error(term, ErrorMessage.PROC_RENAME_DIFF_NUMBER_CHANS, params);
//    }
//    
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//     **/
//  }
//  
//  // Process ::= Process \extchoice Process
//  //ok - verificado em 15/09/2005 �s 19:39
////  public Object visitExtChoiceProcess(ExtChoiceProcess term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  // Process ::= Process \intchoice Process
//  //ok - verificado em 15/09/2005 �s 19:39
////  public Object visitIntChoiceProcess(IntChoiceProcess term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  //n�o existe
////  public Object visitParProcess(ParProcess term)
////  {
////    return visitProcess2(term);
////  }
//
//  // Process ::= Process ; Process
//  //ok - verificado em 15/09/2005 �s 19:39
////  public Object visitSeqProcess(SeqProcess term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  // Process ::= Process \interleave Process
//  //ok - verificado em 15/09/2005 �s 19:39
////  public Object visitInterleaveProcess(InterleaveProcess term)
////  {
////    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
////    addProcessAnn(term, procSignature);
////    
////    return procSignature;
////  }
//
//  // Process ::= Process |[CSExpression]| Process
//  //ok - verificado em 15/09/2005 �s 19:41
//  public ProcessSignature visitParallelProcess(ParallelProcess term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    ProcessSignature procSignature = visitProcess2(term);
//    //addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//
//  // Process ::= Process |[CSExpression | CSExpression]| Process
//  //ok - verificado em 15/09/2005 �s 19:42
//  public ProcessSignature visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
//  {
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    ChanSetType typeCSL = (ChanSetType)term.getLeftAlpha().accept(exprChecker());
//    ChanSetType typeCSR = (ChanSetType)term.getRightAlpha().accept(exprChecker());
//    allPairs.addAll(typeCSL.getChannels().getNameTypePair());
//    allPairs.addAll(typeCSR.getChannels().getNameTypePair());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(allPairs);
//    //
//    
//    ProcessSignature procSignature = visitProcess2(term);
//    //addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }
//
//  // M�TODOS AUXILIARES
//  
//  private boolean checkCallProcessParamTypes(DeclName procName, List<NameTypePair> decs, List<Type2> types){
//    boolean result = true;
//    int i = 0;
//    if(decs.size() == types.size()) {
//      for(NameTypePair pair : decs) {
//        Type2 expectedU = unwrapType(pair.getType());
//        Type2 foundU = unwrapType(types.get(i));
//        if(foundU instanceof UnknownType) {
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), assertZDeclName(procName).getWord(), i+1};
//          error(procName, ErrorMessage.PARAM_PROC_CALL_UNDECLARED_VAR, params);
//          result = false;
//          break;
//        }
//        if (unify(foundU, expectedU) != SUCC) {
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), expectedU, foundU, i, assertZDeclName(procName).getWord()};
//          error(procName, ErrorMessage.PARAM_PROC_CALL_NOT_UNIFY, params);
//          result = false;
//          break;
//        }   
//        i++;
//      }
//    } else {
//      Object [] params = {assertZDeclName(currentProcess()).getWord(), decs.size(), types.size(), assertZDeclName(procName).getWord()};
//      error(procName, ErrorMessage.PROC_CALL_DIFF_NUMBER_EXPRS, params);
//      result = false;
//    }
//    
//    return result;
//  }
//
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
//  // TALVEZ FOSSE MAIS INTERESSANTE AQUI UM VISITOR... TALVEZ EU ESTEJA AMARRANDO
//  // O C�DIGO E QUALQUER ALTERA��O NA ESTRUTURA, QUEBRA ESTE M�TODO...
//  private boolean isSchExprAction(Para para) {
//    boolean result = false;
//    
//    if(para instanceof AxPara) {
//      Decl axDecl = (Decl)((AxPara)para).getZSchText().getZDeclList().get(0);
//      if(axDecl instanceof ConstDecl) {
//        Expr exprAx = ((ConstDecl)axDecl).getExpr();
//        if(exprAx instanceof SchExpr) {
//          ZSchText schText = ((SchExpr)exprAx).getZSchText();
//          ZDeclList decls = schText.getZDeclList();
//          for(Decl decl : decls) {
//            if(decl instanceof InclDecl) {
//              Expr expr = ((InclDecl)decl).getExpr();
//              if(expr instanceof RefExpr) {
//                String refName = ((RefExpr)expr).getZRefName().getWord();
//                String stateName = stateName() != null ? assertZDeclName(stateName()).getWord() : "";
//                if(refName.equals(stateName) 
//                   || refName.equals(ZString.DELTA + stateName) 
//                   || refName.equals(ZString.XI + stateName)
//                   || refName.equals(stateName + "'")) 
//                {
//                  result = true;
//                  break;
//                }
//              }
//            }
//          }
//        }
//      }
//    }
//    
//    return result;
//  }
//
//  private void checkCallProcess(CallProcess term, List<NameTypePair> paramsOrIndexes) {
//    
//    ZDeclName procDecl = factory().createZDeclName(assertZRefName(term.getRefName()));
//    String kindOfProcess = getKindOfProcess(procDecl);
//    List<Type2> typeExprs = new ArrayList<Type2>();    
//    ZExprList exprs = null;
//    
//    // TODO: Check this comment. Old CallType.Gen, GenParam, GenIndex.
//    //
//    //  Regardless the indexes or the parameters, generics must always be checked.       
//    ZExprList zGenActuals = term.getGenActuals() == null ? null : assertZExprList(term.getGenActuals());
//    if (zGenActuals != null && !zGenActuals.isEmpty()) {
//        if(!isGenericProcess(procDecl)){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//        }
//        else {
//            // TODO: Check the generic actuals types
//            // TODO: Check: Why is this check for power type originally (below)? 
//            //             Can't generic actuals be of other types? 
//            List<Type2>typeGenExprs = new ArrayList<Type2>();
//            ZExprList genExprs = zGenActuals;
//            for(Expr genExpr : genExprs) {
//                Type2 type = genExpr.accept(exprChecker());
//                typeGenExprs.add(type);            
//            } 
//            // Check the correspondence between generic formals and actuals.
//            List<DeclName> genParams = getGenParamsProcess(procDecl);
//            if(genParams.size() != typeGenExprs.size()) {
//                Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//                                    genParams.size(), typeGenExprs.size()};
//                error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//            }        
//        }
//    }
//    // Now we check if the parameters are to be considered or not.
//    // CallType.Normal!
//    ZExprList zActuals = term.getActuals() == null ? null : assertZExprList(term.getActuals());
//    if (zActuals == null || zActuals.isEmpty()) {
//        if(!kindOfProcess.equals("NORMAL")){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.PROC_CALL_NEEDS_PARAMS, params);
//        }
//    } 
//    // CallType.Param, CallType.Index
//    else {
//        assert zActuals != null && !zActuals.isEmpty();
//        if (term.getCallType().equals(CallType.Param)) {
//            if(!kindOfProcess.equals("PARAM")){
//              Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//              error(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
//            }
//            else {
//              exprs = zActuals;
//              for(Expr expr : exprs) {
//                Type2 type = expr.accept(exprChecker());
//                typeExprs.add(type);
//              }
//              checkCallProcessParamTypes(procDecl, paramsOrIndexes, typeExprs);
//            }    
//        } else {
//            if(!kindOfProcess.equals("INDEX")){
//              Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//              error(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
//            }
//            else {
//              exprs = zActuals;
//              for(Expr expr : exprs) {
//                Type2 type = expr.accept(exprChecker());
//                typeExprs.add(type);
//              }
//              checkCallProcessParamTypes(procDecl, paramsOrIndexes, typeExprs);
//            }
//        }
//    }
//        
//    /*
//    switch(term.getCallType()) {
//      case Param :
//        if(!kindOfProcess.equals("PARAM")){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
//        }
//        else {
//          exprs = assertZExprList(term.getActuals());
//          for(Expr expr : exprs) {
//            Type2 type = expr.accept(exprChecker());
//            typeExprs.add(type);
//          }
//          checkCall(procDecl, paramsOrIndexes, typeExprs);
//        }
//        break;
//      case Index :
//        if(!kindOfProcess.equals("INDEX")){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
//        }
//        else {
//          exprs = assertZExprList(term.getActuals());
//          for(Expr expr : exprs) {
//            Type2 type = expr.accept(exprChecker());
//            typeExprs.add(type);
//          }
//          checkCall(procDecl, paramsOrIndexes, typeExprs);
//        }
//        break;
//      case Gen :
//        if(!isGenericProcess(procDecl)){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//        }
//        else {
//          exprs = assertZExprList(term.getGenActuals());
//          for(Expr expr : exprs) {
//            Type2 type = expr.accept(exprChecker());
//            // TODO: Check: Why is this check for power type here? Can't generic actuals be of other types?
//            if(!(type instanceof PowerType)) {
//              // ERRO. A EXPRESS�O DEVE SER UM CONJUNTO
//              Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//              error(term, ErrorMessage.IS_NOT_POWER_TYPE_IN_GEN_PROCESS, params);
//              break;
//            }
//            else {
//              typeExprs.add(type);
//            }
//          }
//          List<DeclName> genParams = getGenParamsProcess(procDecl);
//          if(genParams.size() != typeExprs.size()) {
//            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//                                genParams.size(), typeExprs.size()};
//            error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//          }
//        }
//        break;
//      case GenParam :
//        if(!isGenericProcess(procDecl)){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//        }
//        else {
//          ZExprList genExprs = assertZExprList(term.getGenActuals());
//          List<Type2> typeGenExprs = new ArrayList<Type2>();
//          for(Expr genExpr : genExprs) {
//            Type2 type = genExpr.accept(exprChecker());
//            typeGenExprs.add(type);
//          }
//          List<DeclName> genParams = getGenParamsProcess(procDecl);
//          if(genParams.size() != typeGenExprs.size()) {
//            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//                                genParams.size(), typeGenExprs.size()};
//            error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//          }
//          if(!kindOfProcess.equals("PARAM")){
//            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//            error(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
//          }
//          else {
//            exprs = assertZExprList(term.getActuals());
//            for(Expr expr : exprs) {
//              Type2 type = expr.accept(exprChecker());
//              typeExprs.add(type);
//            }
//            checkCall(procDecl, paramsOrIndexes, typeExprs);
//          }
//        }
//        break;
//      case GenIndex :
//        if(!isGenericProcess(procDecl)){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//        }
//        else {
//          ZExprList genExprs = assertZExprList(term.getGenActuals());
//          List<Type2> typeGenExprs = new ArrayList<Type2>();
//          for(Expr genExpr : genExprs) {
//            Type2 type = genExpr.accept(exprChecker());
//            typeGenExprs.add(type);
//          }
//          List<DeclName> genParams = getGenParamsProcess(procDecl);
//          if(genParams.size() != typeGenExprs.size()) {
//            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//                                genParams.size(), typeGenExprs.size()};
//            error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//          }
//          if(!kindOfProcess.equals("INDEX")){
//            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//            error(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
//          }
//          else {
//            exprs = assertZExprList(term.getActuals());
//            for(Expr expr : exprs) {
//              Type2 type = expr.accept(exprChecker());
//              typeExprs.add(type);
//            }
//            checkCall(procDecl, paramsOrIndexes, typeExprs);
//          }
//        }
//        break;
//      case Normal :
//        if(!kindOfProcess.equals("NORMAL")){
//          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.PROC_CALL_NEEDS_PARAMS, params);
//        }
//        break;
//    }
//     */
//    
//  }
///*
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
