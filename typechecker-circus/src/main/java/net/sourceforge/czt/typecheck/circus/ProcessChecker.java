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

import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.typecheck.circus.impl.ProcessInfo;

import static net.sourceforge.czt.z.util.ZUtils.*;
import static net.sourceforge.czt.typecheck.circus.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;
import net.sourceforge.czt.circustools.ast.*;
import net.sourceforge.czt.circustools.visitor.*;
import net.sourceforge.czt.typecheck.circus.util.KindOfProcess;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.util.ZString;

/**
 * Visitor que checa os tipos de processos. Retorna sempre um objeto do tipo
 * ProcessSignature.
 *
 * @author Leo Freitas
 * @author Manuela Xavier
 */
public class ProcessChecker extends Checker<ProcessSignature>
  implements Process1Visitor<ProcessSignature>,
             Process2Visitor<ProcessSignature>,
             IndexedProcessVisitor<ProcessSignature>,
             CallProcessVisitor<ProcessSignature>,
             BasicProcessVisitor<ProcessSignature>,
             //ProcessDVisitor,
             ProcessIteVisitor<ProcessSignature>,
             //ProcessIdxVisitor,             
             ParamProcessVisitor<ProcessSignature>,
             //ParProcessIteVisitor,
             //ExtChoiceProcessIteVisitor,
             //IntChoiceProcessIteVisitor,
             //SeqProcessIteVisitor,
             AlphabetisedParallelProcessIteVisitor<ProcessSignature>,
             //InterleaveProcessIteVisitor,
             ParallelProcessIteVisitor<ProcessSignature>,
             //IntChoiceProcessIdxVisitor,
             //ExtChoiceProcessIdxVisitor,
             AlphabetisedParallelProcessIdxVisitor<ProcessSignature>,
             //ParProcessIdxVisitor,
             //SeqProcessIdxVisitor,
             ParallelProcessIdxVisitor<ProcessSignature>,
             //InterleaveProcessIdxVisitor,
             MuProcessVisitor<ProcessSignature>,
             PrefixingProcessVisitor<ProcessSignature>,
             GuardedProcessVisitor<ProcessSignature>,
             HideProcessVisitor<ProcessSignature>,
             RenameProcessVisitor<ProcessSignature>,
             //ExtChoiceProcessVisitor,
             //IntChoiceProcessVisitor,
             //ParProcessVisitor<ProcessSignature>,
             //SeqProcessVisitor,
             //InterleaveProcessVisitor,
             ParallelProcessVisitor<ProcessSignature>,
             AlphabetisedParallelProcessVisitor<ProcessSignature>
{
    
  //a Z decl checker
  protected net.sourceforge.czt.typecheck.z.DeclChecker zDeclChecker_;

  /** Creates a new instance of ProcessChecker */
  public ProcessChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zDeclChecker_ =
      new net.sourceforge.czt.typecheck.z.DeclChecker(typeChecker);
  }
  
  //ok - verificado em 15/09/2005 �s 19:03
  public ProcessSignature visitProcess1(Process1 term)
  {
    ProcessSignature signature = term.getCircusProcess().accept(processChecker());
    addProcessAnn(term, signature);
    return signature;
  }

  //ok - verificado em 15/09/2005 �s 19:03
  public ProcessSignature visitProcess2(Process2 term)
  {
    ProcessSignature procSigL = term.getLeftProc().accept(processChecker());
    ProcessSignature procSigR = term.getRightProc().accept(processChecker());    
    ProcessSignature result = joinProcessSignature(procSigL, procSigR);
    addProcessAnn(term, result);
    return result;
  }

  // ParamProcess ::= Declaration \odot Process
  //ok - verificado em 15/09/2005 �s 19:05
  public ProcessSignature visitIndexedProcess(IndexedProcess term)
  {
    ZDeclList zdl = term.getZDeclList();        
    CircusProcess proc = term.getCircusProcess();
    
    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    List<Object> paramsError = new ArrayList<Object>();
    paramsError.add(assertZDeclName(currentProcess()).getWord());

    // novo escopo devido aos canais implicitos
    localCircTypeEnv().enterScope();
    
    for(Decl d : zdl){
      if (!(d instanceof VarDecl))
          throw new UnsupportedOperationException("Indexed processes accept only VarDecl!");
      VarDecl decl = (VarDecl)d;
      List<NameTypePair> pairs = decl.accept(declChecker());
      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_INDEX_IN_PROCESS, paramsError);
    }

    // atualiza informa��es sobre o processo
    ProcessInfo procInfo = getProcessInfo(currentProcess());
    procInfo.setKindOfProcess(KindOfProcess.INDEX);
    procInfo.setParamsOrIndexes(allPairs);
    
    ProcessSignature procSignature = proc.accept(processChecker());
    ProcessSignature signature = cloneProcessSignature(procSignature);
    Signature sig = factory().createSignature(allPairs);
    signature.setParamsOrIndexes(sig);

    // extrai os canais implicitos a partir dos canais usados pelo processo
    List<NameTypePair> usedChans = localCircTypeEnv().getUsedChans();
    List<NameTypePair> implicitChans = extractImplicitChans(allPairs, usedChans);
    //
    
    localCircTypeEnv().exitScope();

    // adiciona os canais usados...
    localCircTypeEnv().addUsedChans(implicitChans);
    //
    
    addProcessAnn(term, signature);
        
    return signature;
  }
  
  // ParamProcess ::= Declaration @ Process
  //ok - verificado em 15/09/2005 �s 19:08
  public ProcessSignature visitParamProcess(ParamProcess term)
  {
    ZDeclList decls = term.getZDeclList();            
    CircusProcess proc = term.getCircusProcess();

    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    List<Object> paramsError = new ArrayList<Object>();
    paramsError.add(assertZDeclName(currentProcess()).getWord());
    
    for(Decl d : decls){
        if (!(d instanceof VarDecl))
          throw new UnsupportedOperationException("Param processes accept only VarDecl!");
      VarDecl decl = (VarDecl)d;
      List<NameTypePair> pairs = decl.accept(declChecker());
      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_PARAM_IN_PROCESS, paramsError);
    }
    
    // atualiza informa��es sobre o processo
    ProcessInfo procInfo = getProcessInfo(currentProcess());
    procInfo.setKindOfProcess(KindOfProcess.PARAM);
    procInfo.setParamsOrIndexes(allPairs);
    
    typeEnv().enterScope();

    typeEnv().add(allPairs);
//    localCircTypeEnv().addCurrentParamsIndexes(allPairs);
    
    ProcessSignature procSig = proc.accept(processChecker());
    ProcessSignature procSignature = cloneProcessSignature(procSig);
    Signature sig = factory().createSignature(allPairs);
    procSignature.setParamsOrIndexes(sig);
    
    typeEnv().exitScope();
    
    addProcessAnn(term, procSignature);
    
    return procSignature;
  }
  
  // Process ::= begin PParagraph* state StateParagraph PParagraph* @ Action end
  // Process ::= begin PParagraph* @ Action end
  //ok - verificado em 15/09/2005 �s 19:11
  public ProcessSignature visitBasicProcess(BasicProcess term)
  {
    BasicProcessSignature procSignature = factory().createBasicProcessSignature();
    
    RefName state = term.getStateSchema();
    
    if(state != null) {
      setStateName(assertZRefName(state).getDecl());
    }
    localCircTypeEnv().getOnTheFlyActions().addAll(term.getOnTheFlyActionPara());
    
    List<Para> zParas = term.getZPara();
    List<NameTypePair> pairs = new ArrayList<NameTypePair>();
    
    for(Para zPara : zParas){

      Signature signature = zPara.accept(paraChecker());

      if(state != null && isSchExprAction(zPara)) {
        NameTypePair pairSig = (NameTypePair)signature.getNameTypePair().get(0);
        ZDeclName actionName = pairSig.getZDeclName();
        SchemaType schType = (SchemaType)((PowerType)pairSig.getType()).getType();
        Signature vars = schType.getSignature();
        
        // cria um actionSignature aqui pois � um caso especial de zPara que
        // o parser n�o tem como identificar se � ou n�o uma a��o.
        // Se o esquema referencia o estado, � a��o!
        ActionSignature actSig = factory().createActionSignature();
        actSig.setActionName(actionName);
        actSig.setLocalVarsSignature(vars);
        // adiciona a a��o na lista de a��es do TypeChecker
        if(!localCircTypeEnv().addAction(actionName)) {
          Object [] params = {actionName.getWord(), assertZDeclName(currentProcess()).getWord()};
          error(term, ErrorMessage.REDECLARED_ACTION_NAME, params);
        }

        // armazena o par�grafo como uma a��o na assinatura do processo
        procSignature.getActionsSignature().add(actSig);

//        ActionType actType = factory().createActionType(actSig);
//        typeEnv().add(actionName, actType);

        typeEnv().add(pairSig);
        
      }
      else {
        procSignature.getLocalZDeclsSignature().add(signature);

        pairs = (List<NameTypePair>)signature.getNameTypePair();
        typeEnv().add(pairs);

        if(state != null && procSignature.getStateSignature() == null) {
          for(NameTypePair pair : pairs){
            if(pair.getDeclName().equals(assertZRefName(state).getDecl())) {
              List<NameTypePair> listPair = new ArrayList<NameTypePair>();
              listPair.add(pair);
              Signature stateSig = factory().createSignature(listPair);
              procSignature.setStateSignature(stateSig);
              addVarsState(pair, term);
              break;
            }
          }
        }
      } 
    }

    List<ActionPara> actions = term.getCircusActionPara();
    
    for(ActionPara action : actions) {
      Signature signature = action.accept(paraChecker());
      ActionType actionType = (ActionType)((NameTypePair)signature.getNameTypePair().get(0)).getType();
      ActionSignature actionSignature = actionType.getActionSignature();
      procSignature.getActionsSignature().add(actionSignature);
    }
    
    List<NameSetPara> namesets = term.getCircusNameSetPara();
    
    for(NameSetPara nameset : namesets) {
      Signature namesetSignature = nameset.accept(paraChecker());
      DeclName name = ((NameTypePair)namesetSignature.getNameTypePair().get(0)).getDeclName();
      procSignature.getDeclNameSets().add(name);
    }
    
    CircusAction mainAction = term.getMainAction();
    ActionSignature mainActionSig = mainAction.accept(actionChecker());
    ActionSignature mainSignature = cloneActionSignature(mainActionSig);
    mainSignature.setActionName(factory().createZDeclName("$$mainAction", null, null));
    
    procSignature.getActionsSignature().add(mainSignature);
    
    addProcessAnn(term, procSignature);

    return procSignature;
    
  }

  // Process ::= N
  // Process ::= N(Expression+)
  // Process ::= N[Expression+]
  // Process ::= N \lfloor Expression+ \rfloor
  // Process ::= (Declaration @ Process)(Expression+)
  // Process ::= (Declaration \odot Process) \lfloor Expression+ \rfloor
  // Process ::= (\mu N @ Declaration @ Process)(Expression+)
  // Process ::= (\mu N @ Declaration \odot Process) \lfloor Expression+ \rfloor
  //ok - verificado em 15/09/2005 �s 19:18
  public ProcessSignature visitCallProcess(CallProcess term)
  {

    ProcessSignature procSignature = factory().createProcessSignature();
    RefName procRef = term.getRefName();
    ZDeclName procDecl = factory().createZDeclName(assertZRefName(procRef));
    
    String nameRefProc = procDecl.getWord();
    if(nameRefProc.startsWith("$$implicitProcess_")) {
      // pegar da lista de processos implicitos, fazer a verifica��o e incluir no
      //SectTypeEnv!!
      List<ProcessPara> implicitProcs = (List<ProcessPara>)onTheFlyProcesses();
      for(ProcessPara implicitProc : implicitProcs) {
        if(nameRefProc.equals(assertZDeclName(implicitProc.getDeclName()).getWord())) {
          Signature implicitProcSig = implicitProc.accept(paraChecker());
          // a assinatura de um processo sempre ter� apenas um par
          NameTypePair pair = (NameTypePair)implicitProcSig.getNameTypePair().get(0);
          //if the name already exists globally, raise an error
          if (sectTypeEnv().add(pair.getZDeclName(), pair.getType()) != null) {
            Object [] params = {pair.getDeclName()};
            error(pair.getDeclName(), ErrorMessage.REDECLARED_GLOBAL_NAME, params);
          }
        }
      }
    }
    
    // verifica se � uma chamada a um processo mu
    if(isMuProcess(procDecl)) {         
      ZExprList zActuals = term.getActuals() == null ? null : assertZExprList(term.getActuals());      
      if(zActuals != null && !zActuals.isEmpty()) {
        Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
        error(term, ErrorMessage.MU_PROC_CALL_ERROR, params);
      }
    }// caso n�o seja uma chamada ao processo mu
    else {
      Type typeRefName = (Type)sectTypeEnv().getType(assertZRefName(procRef));

      if(!(typeRefName instanceof UnknownType)) {

        if(!isProcess(procDecl)) {
          Object [] params = {assertZDeclName(currentProcess()).getWord(), assertZDeclName(procDecl).getWord()};
          error(term, ErrorMessage.IS_NOT_PROCESS_NAME, params);
        } else {
          ProcessType procType = (ProcessType)typeRefName;
          procSignature = procType.getProcessSignature();
          // adiciona os canais usados...
          List<NameTypePair> usedChans = getUsedChannels(procDecl);
          localCircTypeEnv().addUsedChans(usedChans);
          //

          List<NameTypePair> paramsOrIndexes = null;
          if(procSignature.getParamsOrIndexes() != null) {
            paramsOrIndexes = procSignature.getParamsOrIndexes().getNameTypePair();
          }
          // chama um m�todo auxiliar que ir� verificar se a chamada est� correta
          checkCallProcess(term, paramsOrIndexes);
        }
      } 
      else {
        if(!(procDecl.equals(currentProcess()))){
//          Object [] params = {currentProcess().getWord(), procDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_PROCESS_NAME, params);
          if (!containsObject(paraErrors(), term)) {
            paraErrors().add(term);
          }
        }
        else {
          // tratamento especial para o caso de chamada recursiva          
          List<NameTypePair> paramsOrIndexes = getProcessInfo(procDecl).getParamsOrIndexes();
          // chama um m�todo auxiliar que ir� verificar se a chamada est� correta
          checkCallProcess(term, paramsOrIndexes);
        }
      }
    }
    
    addProcessAnn(term, procSignature);
    
    return procSignature;
  }
  
  //ok - verificado em 15/09/2005 �s 19:18
//  public Object visitProcessD(ProcessD term)
//  {
//    return term.accept(processChecker());
//  }
  
  //ok - verificado em 15/09/2005 �s 19:21
  public ProcessSignature visitProcessIte(ProcessIte term)
  {
    ZDeclList decs = term.getZDeclList();
    CircusProcess proc = term.getCircusProcess();

    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    List<Object> paramsError = new ArrayList<Object>();
    paramsError.add(assertZDeclName(currentProcess()).getWord());

    for(Decl d : decs) {
        if (!(d instanceof VarDecl))
          throw new UnsupportedOperationException("Iterated processes accept only VarDecl!");
       VarDecl dec = (VarDecl)d;
      boolean declOK = false;
      if(dec.getExpr() instanceof SetExpr) {
        declOK = true;
      }
      else if(dec.getExpr() instanceof ApplExpr) {
        ApplExpr applExpr = (ApplExpr)dec.getExpr();
        if(applExpr.getLeftExpr() instanceof RefExpr) {
          if(assertZRefName(((RefExpr)applExpr.getLeftExpr()).getRefName()).getWord().equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK)) {
            declOK = true;
          }
        }
      }
      List<NameTypePair> pairs = dec.accept(declChecker());
      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_VAR_IN_PROCESS_ITE, paramsError);
      if(!declOK) {
        Object [] params = {assertZDeclName(currentProcess()).getWord()};
        error(term, ErrorMessage.INFINITY_VALUES_IN_PROCESS_ITE, params);
        break;
      }
    }

    typeEnv().enterScope();

    typeEnv().add(allPairs);
    ProcessSignature procSig = proc.accept(processChecker());
    ProcessSignature procSignature = cloneProcessSignature(procSig);
    Signature sig = factory().createSignature(allPairs);
    procSignature.setParamsOrIndexes(sig);
    
    typeEnv().exitScope();
    
    // TODO: Check: added from the other visitors. It is to have the same effect.
    addProcessAnn(term, procSignature);

    return procSignature;
  }
  
  // existe?!?
  //ok   TODO: As ProcessIdx is a child of ProcessIte, it will go there directly.
//  public Object visitProcessIdx(ProcessIdx term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIte(term);
//    return procSignature;
//  }
  
  // existe?!?
  //ok
//  public Object visitParProcessIte(ParProcessIte term)
//  {
//    return visitProcessIte(term);
//  }
  
  // Process ::= \Extchoice Declaration @ Process
  //ok - verificado em 15/09/2005 �s 19:24
//  public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIte(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= \Intchoice Declaration @ Process
  //ok - verificado em 15/09/2005 �s 19:25
//  public Object visitIntChoiceProcessIte(IntChoiceProcessIte term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIte(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= \Semi Declaration @ Process
  //ok - verificado em 15/09/2005 �s 19:25
//  public Object visitSeqProcessIte(SeqProcessIte term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIte(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= \Parallel Declaration @ |[CSExpression]| Process
  //ok - verificado em 15/09/2005 �s 19:27
  public ProcessSignature visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //
    ProcessSignature procSignature = visitProcessIte(term);
    // TODO: Check: already added at visitProcessIte(term).
    //addProcessAnn(term, procSignature);
    
    return procSignature;
  }

  // Process ::= \Interleave Declaration @ Process
  //ok - verificado em 15/09/2005 �s 19:28
//  public Object visitInterleaveProcessIte(InterleaveProcessIte term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIte(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= |[CSExpression]| Declaration @ Process
  //ok - verificado em 15/09/2005 �s 19:28
  public ProcessSignature visitParallelProcessIte(ParallelProcessIte term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    ProcessSignature procSignature = visitProcessIte(term);
    // TODO: Check: already added at visitProcessIte(term).
    //addProcessAnn(term, procSignature);
    
    return procSignature;
  }
  
  //n�o existe mais
//  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  //n�o existe mais
//  public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  //n�o existe mais
  public ProcessSignature visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    ProcessSignature procSignature = visitProcessIte(term);
    // TODO: Check: already added at visitProcessIte(term).
    //addProcessAnn(term, procSignature);
    
    return procSignature;
  }

  //n�o existe mais
//  public Object visitParProcessIdx(ParProcessIdx term)
//  {
//    return visitProcessIdx(term);
//  }
//  
  //n�o existe mais
//  public Object visitSeqProcessIdx(SeqProcessIdx term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  //n�o existe mais
  public ProcessSignature visitParallelProcessIdx(ParallelProcessIdx term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    ProcessSignature procSignature = visitProcessIte(term);
    // TODO: Check: already added at visitProcessIte(term).
    //addProcessAnn(term, procSignature);
    
    return procSignature;
  }

  //n�o existe mais
//  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcessIdx(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= \mu N @ Process
  // Process ::= \mu N @ ParamProcess
  //ok - verificado em 15/09/2005 �s 19:31
  public ProcessSignature visitMuProcess(MuProcess term)
  {
    DeclName name = term.getDeclName();
    CircusProcess proc = term.getCircusProcess();

    addMuProcess(name);    
    ProcessSignature signature = proc.accept(processChecker());
    removeMuProcess(name);
    
    addProcessAnn(term, signature);
    
    return signature;
  }
  
  // Process ::= Communication -> Process
  //ok - verificado em 15/09/2005 �s 19:32
  public ProcessSignature visitPrefixingProcess(PrefixingProcess term)
  {
    RefName chanName = term.getCommunication().getChanName();
    CircusProcess proc = term.getCircusProcess();
    
    List<NameTypePair> inputVars = term.getCommunication().accept(communicChecker());

    typeEnv().enterScope();

    // ADICIONAR NO AMBIENTE AS VARIA��ES DAS VARI�VEIS DECLARADAS
//    typeEnv().add(inputVars);
    addVars(inputVars);

    ProcessSignature procSig = proc.accept(processChecker());

    typeEnv().exitScope();

    addProcessAnn(term, procSig);    
    
    return procSig;
  }

  // Process ::= Predicate & Process
  //ok - verificado em 15/09/2005 �s 19:36
  public ProcessSignature visitGuardedProcess(GuardedProcess term)
  {
    term.getPred().accept(predChecker());
    ProcessSignature signature = term.getCircusProcess().accept(processChecker());
    addProcessAnn(term, signature);
    
    return signature;
  }

  // Process ::= Process \ CSExpression
  //ok - verificado em 15/09/2005 �s 19:36
  public ProcessSignature visitHideProcess(HideProcess term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    ProcessSignature signature = term.getCircusProcess().accept(processChecker());
    addProcessAnn(term,  signature);
    
    return signature;
  }
  
  // Process ::= Process[N+ := N+]
  //ok - verificado em 15/09/2005 �s 19:38
  public ProcessSignature visitRenameProcess(RenameProcess term)
  {
    ProcessSignature procSignature = term.getCircusProcess().accept(processChecker());
    ZRenameList zrl = term.getZRenameList();    
    int i = 0;
    for(NewOldPair nop : zrl) {
        ZDeclName oldName = factory().createZDeclName(nop.getZRefName().getWord(), null, null);
        ZDeclName newName = factory().createZDeclName(nop.getZDeclName().getWord(), null, null);
        if(!isChannel(oldName) || !isChannel(newName)) {
          Object [] params = {assertZDeclName(currentProcess()).getWord(), 
                  assertZDeclName(procSignature.getProcessName()).getWord()};
          error(term, ErrorMessage.NAMES_ARE_NOT_CHANNELS_IN_PROC_RENAME, params);
          break;
        } else {
          Type oldType = getChannelType(oldName);
          Type newType = getChannelType(newName);
          Type2 expectedU = unwrapType(oldType);
          Type2 foundU = unwrapType(newType);
          if (unify(foundU, expectedU) != SUCC) {
            Object [] params = {expectedU, foundU, i+1, assertZDeclName(procSignature.getProcessName()).getWord()};
            error(term, ErrorMessage.PROC_RENAME_NOT_UNIFY, params);
            break;
          }   
          // adiciona os canais usados...
          List<NameTypePair> usedChans = new ArrayList<NameTypePair>();
          NameTypePair oldC = factory().createNameTypePair(oldName, oldType);
          usedChans.add(oldC);
          NameTypePair newC = factory().createNameTypePair(newName, newType);
          usedChans.add(newC);
          localCircTypeEnv().addUsedChans(usedChans);                   
        }
        i++;
    }
    addProcessAnn(term, procSignature);    
    return procSignature;
    
    /*
    ProcessSignature procSignature = term.getCircusProcess().accept(processChecker());
    List<RefName> oldNames = (List<RefName>)term.getOldNames();
    List<RefName> newNames = (List<RefName>)term.getNewNames();
    
    if(oldNames.size() == newNames.size()) {
      int i = 0;
      for(RefName oldChan : (List<RefName>)oldNames) {
        DeclName oldName = factory().createDeclName(oldChan.getWord(), null, null);
        DeclName newName = factory().createDeclName(newNames.get(i).getWord(), null, null);
        if(!isChannel(oldName.getWord()) || !isChannel(newName.getWord())) {
          Object [] params = {currentProcess().getWord(), procSignature.getProcessName().getWord()};
          error(term, ErrorMessage.NAMES_ARE_NOT_CHANNELS_IN_PROC_RENAME, params);
          break;
        } else {
          Type oldType = getChannelType(oldName.getWord());
          Type newType = getChannelType(newName.getWord());
          Type2 expectedU = unwrapType(oldType);
          Type2 foundU = unwrapType(newType);
          if (unify(foundU, expectedU) != SUCC) {
            Object [] params = {expectedU, foundU, i+1, procSignature.getProcessName().getWord()};
            error(term, ErrorMessage.PROC_RENAME_NOT_UNIFY, params);
            break;
          }   
          // adiciona os canais usados...
          List<NameTypePair> usedChans = list();
          NameTypePair oldC = factory().createNameTypePair(oldName, oldType);
          usedChans.add(oldC);
          NameTypePair newC = factory().createNameTypePair(newName, newType);
          usedChans.add(newC);
          localCircTypeEnv().addUsedChans(usedChans);
          //
          i++;
        }
      }
    } else {
      Object [] params = {oldNames.size(), newNames.size(), procSignature.getProcessName().getWord()};
      error(term, ErrorMessage.PROC_RENAME_DIFF_NUMBER_CHANS, params);
    }
    
    addProcessAnn(term, procSignature);
    
    return procSignature;
     **/
  }
  
  // Process ::= Process \extchoice Process
  //ok - verificado em 15/09/2005 �s 19:39
//  public Object visitExtChoiceProcess(ExtChoiceProcess term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= Process \intchoice Process
  //ok - verificado em 15/09/2005 �s 19:39
//  public Object visitIntChoiceProcess(IntChoiceProcess term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  //n�o existe
//  public Object visitParProcess(ParProcess term)
//  {
//    return visitProcess2(term);
//  }

  // Process ::= Process ; Process
  //ok - verificado em 15/09/2005 �s 19:39
//  public Object visitSeqProcess(SeqProcess term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= Process \interleave Process
  //ok - verificado em 15/09/2005 �s 19:39
//  public Object visitInterleaveProcess(InterleaveProcess term)
//  {
//    ProcessSignature procSignature = (ProcessSignature)visitProcess2(term);
//    addProcessAnn(term, procSignature);
//    
//    return procSignature;
//  }

  // Process ::= Process |[CSExpression]| Process
  //ok - verificado em 15/09/2005 �s 19:41
  public ProcessSignature visitParallelProcess(ParallelProcess term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    ProcessSignature procSignature = visitProcess2(term);
    //addProcessAnn(term, procSignature);
    
    return procSignature;
  }

  // Process ::= Process |[CSExpression | CSExpression]| Process
  //ok - verificado em 15/09/2005 �s 19:42
  public ProcessSignature visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    ChanSetType typeCSL = (ChanSetType)term.getLeftAlpha().accept(exprChecker());
    ChanSetType typeCSR = (ChanSetType)term.getRightAlpha().accept(exprChecker());
    allPairs.addAll(typeCSL.getChannels().getNameTypePair());
    allPairs.addAll(typeCSR.getChannels().getNameTypePair());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(allPairs);
    //
    
    ProcessSignature procSignature = visitProcess2(term);
    //addProcessAnn(term, procSignature);
    
    return procSignature;
  }

  // M�TODOS AUXILIARES
  
  private boolean checkCallProcessParamTypes(DeclName procName, List<NameTypePair> decs, List<Type2> types){
    boolean result = true;
    int i = 0;
    if(decs.size() == types.size()) {
      for(NameTypePair pair : decs) {
        Type2 expectedU = unwrapType(pair.getType());
        Type2 foundU = unwrapType(types.get(i));
        if(foundU instanceof UnknownType) {
          Object [] params = {assertZDeclName(currentProcess()).getWord(), assertZDeclName(procName).getWord(), i+1};
          error(procName, ErrorMessage.PARAM_PROC_CALL_UNDECLARED_VAR, params);
          result = false;
          break;
        }
        if (unify(foundU, expectedU) != SUCC) {
          Object [] params = {assertZDeclName(currentProcess()).getWord(), expectedU, foundU, i, assertZDeclName(procName).getWord()};
          error(procName, ErrorMessage.PARAM_PROC_CALL_NOT_UNIFY, params);
          result = false;
          break;
        }   
        i++;
      }
    } else {
      Object [] params = {assertZDeclName(currentProcess()).getWord(), decs.size(), types.size(), assertZDeclName(procName).getWord()};
      error(procName, ErrorMessage.PROC_CALL_DIFF_NUMBER_EXPRS, params);
      result = false;
    }
    
    return result;
  }

  private List<NameTypePair> extractImplicitChans(List<NameTypePair> decls, List<NameTypePair> usedChans) {
    List<NameTypePair> result = new ArrayList<NameTypePair>();
    
    for(NameTypePair chan : usedChans) {
      ZDeclName chanName = chan.getZDeclName();
      Type chanType = chan.getType();
      String newName = chanName.getWord();
      List<Type2> newType = new ArrayList<Type2>();
      for(NameTypePair decl : decls) {
        newName = newName + "\\_" + decl.getZDeclName().getWord();
        // TODO: Check why not unwrapType here
        // newType.add(decl.getType());
        newType.add(unwrapType(decl.getType()));
      }
      
      if(chanType instanceof GivenType) {
        ZDeclName name = ((GivenType)chanType).getName();
        if(!(name.getWord().equals("Synch"))) {
          newType.add((GivenType)chanType);
        }
      } else {
        // TODO: Check why not unwrapType here
        // newType.add(chanType);
        newType.add(unwrapType(chanType));
      }

      ZDeclName newChanName = factory().createZDeclName(newName, null, null);
      ProdType newChanType = factory().createProdType(newType);
      NameTypePair pair = factory().createNameTypePair(newChanName, newChanType);

      if(!result.contains(pair)) {
        result.add(pair);
      }
      
      if(isGenericChannel(chanName)) {
        localCircTypeEnv().addGenericImplicitChan(newChanName);
      }
    }
    return result;
  }

  private void addVarsState(NameTypePair pair, BasicProcess term) {
    ZDeclName stateName = pair.getZDeclName();
    SchemaType schType = (SchemaType)((PowerType)pair.getType()).getType();
    List<NameTypePair> varsState = schType.getSignature().getNameTypePair();
    for(NameTypePair varState : varsState) {
      if(!localCircTypeEnv().addStateVar(varState)){
        Object [] params = {varState.getZDeclName().getWord(), stateName.getWord()};
        error(term, ErrorMessage.REDECLARED_LOCAL_NAME, params);
      } 
    }

    ZDeclName delta = factory().createZDeclName(ZString.DELTA + stateName.getWord(), null, null);
    typeEnv().add(delta, pair.getType());
    ZDeclName xi = factory().createZDeclName(ZString.XI + stateName.getWord(), null, null);
    typeEnv().add(xi, pair.getType());
    // TODO: Check strokes here! Seems very strange.
    ZDeclName prime = factory().createZDeclName(stateName.getWord() + "'", null, null);
    typeEnv().add(prime, pair.getType());
  }

  // TALVEZ FOSSE MAIS INTERESSANTE AQUI UM VISITOR... TALVEZ EU ESTEJA AMARRANDO
  // O C�DIGO E QUALQUER ALTERA��O NA ESTRUTURA, QUEBRA ESTE M�TODO...
  private boolean isSchExprAction(Para para) {
    boolean result = false;
    
    if(para instanceof AxPara) {
      Decl axDecl = (Decl)((AxPara)para).getZSchText().getZDeclList().get(0);
      if(axDecl instanceof ConstDecl) {
        Expr exprAx = ((ConstDecl)axDecl).getExpr();
        if(exprAx instanceof SchExpr) {
          ZSchText schText = ((SchExpr)exprAx).getZSchText();
          ZDeclList decls = schText.getZDeclList();
          for(Decl decl : decls) {
            if(decl instanceof InclDecl) {
              Expr expr = ((InclDecl)decl).getExpr();
              if(expr instanceof RefExpr) {
                String refName = ((RefExpr)expr).getZRefName().getWord();
                String stateName = stateName() != null ? assertZDeclName(stateName()).getWord() : "";
                if(refName.equals(stateName) 
                   || refName.equals(ZString.DELTA + stateName) 
                   || refName.equals(ZString.XI + stateName)
                   || refName.equals(stateName + "'")) 
                {
                  result = true;
                  break;
                }
              }
            }
          }
        }
      }
    }
    
    return result;
  }

  private void checkCallProcess(CallProcess term, List<NameTypePair> paramsOrIndexes) {
    
    ZDeclName procDecl = factory().createZDeclName(assertZRefName(term.getRefName()));
    String kindOfProcess = getKindOfProcess(procDecl);
    List<Type2> typeExprs = new ArrayList<Type2>();    
    ZExprList exprs = null;
    
    // TODO: Check this comment. Old CallType.Gen, GenParam, GenIndex.
    //
    //  Regardless the indexes or the parameters, generics must always be checked.       
    ZExprList zGenActuals = term.getGenActuals() == null ? null : assertZExprList(term.getGenActuals());
    if (zGenActuals != null && !zGenActuals.isEmpty()) {
        if(!isGenericProcess(procDecl)){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
        }
        else {
            // TODO: Check the generic actuals types
            // TODO: Check: Why is this check for power type originally (below)? 
            //             Can't generic actuals be of other types? 
            List<Type2>typeGenExprs = new ArrayList<Type2>();
            ZExprList genExprs = zGenActuals;
            for(Expr genExpr : genExprs) {
                Type2 type = genExpr.accept(exprChecker());
                typeGenExprs.add(type);            
            } 
            // Check the correspondence between generic formals and actuals.
            List<DeclName> genParams = getGenParamsProcess(procDecl);
            if(genParams.size() != typeGenExprs.size()) {
                Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
                                    genParams.size(), typeGenExprs.size()};
                error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
            }        
        }
    }
    // Now we check if the parameters are to be considered or not.
    // CallType.Normal!
    ZExprList zActuals = term.getActuals() == null ? null : assertZExprList(term.getActuals());
    if (zActuals == null || zActuals.isEmpty()) {
        if(!kindOfProcess.equals("NORMAL")){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.PROC_CALL_NEEDS_PARAMS, params);
        }
    } 
    // CallType.Param, CallType.Index
    else {
        assert zActuals != null && !zActuals.isEmpty();
        if (term.getCallType().equals(CallType.Param)) {
            if(!kindOfProcess.equals("PARAM")){
              Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
              error(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
            }
            else {
              exprs = zActuals;
              for(Expr expr : exprs) {
                Type2 type = expr.accept(exprChecker());
                typeExprs.add(type);
              }
              checkCallProcessParamTypes(procDecl, paramsOrIndexes, typeExprs);
            }    
        } else {
            if(!kindOfProcess.equals("INDEX")){
              Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
              error(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
            }
            else {
              exprs = zActuals;
              for(Expr expr : exprs) {
                Type2 type = expr.accept(exprChecker());
                typeExprs.add(type);
              }
              checkCallProcessParamTypes(procDecl, paramsOrIndexes, typeExprs);
            }
        }
    }
        
    /*
    switch(term.getCallType()) {
      case Param :
        if(!kindOfProcess.equals("PARAM")){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
        }
        else {
          exprs = assertZExprList(term.getActuals());
          for(Expr expr : exprs) {
            Type2 type = expr.accept(exprChecker());
            typeExprs.add(type);
          }
          checkCall(procDecl, paramsOrIndexes, typeExprs);
        }
        break;
      case Index :
        if(!kindOfProcess.equals("INDEX")){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
        }
        else {
          exprs = assertZExprList(term.getActuals());
          for(Expr expr : exprs) {
            Type2 type = expr.accept(exprChecker());
            typeExprs.add(type);
          }
          checkCall(procDecl, paramsOrIndexes, typeExprs);
        }
        break;
      case Gen :
        if(!isGenericProcess(procDecl)){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
        }
        else {
          exprs = assertZExprList(term.getGenActuals());
          for(Expr expr : exprs) {
            Type2 type = expr.accept(exprChecker());
            // TODO: Check: Why is this check for power type here? Can't generic actuals be of other types?
            if(!(type instanceof PowerType)) {
              // ERRO. A EXPRESS�O DEVE SER UM CONJUNTO
              Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
              error(term, ErrorMessage.IS_NOT_POWER_TYPE_IN_GEN_PROCESS, params);
              break;
            }
            else {
              typeExprs.add(type);
            }
          }
          List<DeclName> genParams = getGenParamsProcess(procDecl);
          if(genParams.size() != typeExprs.size()) {
            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
                                genParams.size(), typeExprs.size()};
            error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
          }
        }
        break;
      case GenParam :
        if(!isGenericProcess(procDecl)){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
        }
        else {
          ZExprList genExprs = assertZExprList(term.getGenActuals());
          List<Type2> typeGenExprs = new ArrayList<Type2>();
          for(Expr genExpr : genExprs) {
            Type2 type = genExpr.accept(exprChecker());
            typeGenExprs.add(type);
          }
          List<DeclName> genParams = getGenParamsProcess(procDecl);
          if(genParams.size() != typeGenExprs.size()) {
            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
                                genParams.size(), typeGenExprs.size()};
            error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
          }
          if(!kindOfProcess.equals("PARAM")){
            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
            error(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
          }
          else {
            exprs = assertZExprList(term.getActuals());
            for(Expr expr : exprs) {
              Type2 type = expr.accept(exprChecker());
              typeExprs.add(type);
            }
            checkCall(procDecl, paramsOrIndexes, typeExprs);
          }
        }
        break;
      case GenIndex :
        if(!isGenericProcess(procDecl)){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
        }
        else {
          ZExprList genExprs = assertZExprList(term.getGenActuals());
          List<Type2> typeGenExprs = new ArrayList<Type2>();
          for(Expr genExpr : genExprs) {
            Type2 type = genExpr.accept(exprChecker());
            typeGenExprs.add(type);
          }
          List<DeclName> genParams = getGenParamsProcess(procDecl);
          if(genParams.size() != typeGenExprs.size()) {
            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
                                genParams.size(), typeGenExprs.size()};
            error(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
          }
          if(!kindOfProcess.equals("INDEX")){
            Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
            error(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
          }
          else {
            exprs = assertZExprList(term.getActuals());
            for(Expr expr : exprs) {
              Type2 type = expr.accept(exprChecker());
              typeExprs.add(type);
            }
            checkCall(procDecl, paramsOrIndexes, typeExprs);
          }
        }
        break;
      case Normal :
        if(!kindOfProcess.equals("NORMAL")){
          Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
          error(term, ErrorMessage.PROC_CALL_NEEDS_PARAMS, params);
        }
        break;
    }
     */
    
  }
/*
  private List axParaSchemaToSchExpr(AxPara axp) {
    ConstDecl cdecl = (ConstDecl)axp.getSchText().getDecl().get(0);
    List result = list();
    result.add(cdecl.getDeclName());
    result.add((SchExpr)cdecl.getExpr());
    return result;
//    return (SchExpr)cdecl.getExpr();
  }
*/
}