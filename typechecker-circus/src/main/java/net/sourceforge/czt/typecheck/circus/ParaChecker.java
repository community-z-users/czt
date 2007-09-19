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

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.TransformerParaVisitor;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZNameList;


/**
 * This visitor adds signature annotations to the paragraphs being checked.
 * That is, if no signature annotation is present, one is added. If one is present
 * and contains variable types, those variable types are updated with the new one.
 * Otherwise, if there are no variable types on an old signature, it is just overridden
 * with the updated signature. Clash of global name clashing is caught at
 * #z.Checker.checkParaList, which is called within #z.SpecChecker.visitZParaList.
 *
 * @author Leo Freitas
 * @author Manuela Xavier
 */
public class ParaChecker
  extends Checker<Signature>
  implements
  ChannelParaVisitor<Signature>,
  ChannelSetParaVisitor<Signature>,
  ProcessParaVisitor<Signature>,
  ActionParaVisitor<Signature>,
  NameSetParaVisitor<Signature>,
  TransformerParaVisitor<Signature>
{
  
  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;
  
  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    isWithinProcessParaScope_ = false;
    zParaChecker_ =
      new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);
  }
  
  protected void checkProcessParaScope(String paraKind, Name name)
  {
    if (!isWithinProcessParaScope())
    {
      Object[] params = { paraKind, aName };
      error(term, ErrorMessage.INVALID_PROCESS_PARA_SCOPE, params);
    }
  }
  
  /**
   * For a general terms (i.e. all other Para subclasses), we just apply Z typechecking
   */
  public Signature visitTerm(Term term)
  {
    // CircusParagraph ::= Paragraph
    return term.accept(zParaChecker_);
  }
  
  /**
   * Type checks all ChannelDecl within the given ChannelPara using
   * the circus.DeclChecker, and then adds the resulting signature as
   * an annotation within the given term.
   */
  public Signature visitChannelPara(ChannelPara term)
  {
    // CircusParagraph ::= channel CDeclaration
    
    // visit all ChannelDecl within the ZDeclList of term
    // this uses the quite elegant (yet intricated) typechecker architecture
    // to use: z.DeclChecker.visitZDeclList(), and circus.DeclChecker.visitChannelDecl().
    List<NameTypePair> pairs = term.getZDeclList().accept(declChecker());
    
    //create the signature for this paragraph and add it as an annotation
    Signature signature = factory().createSignature(pairs);
    
    //creates a new, overrides existing, or updates variable signatures.
    addSignatureAnn(term, signature);
    
    return signature;
  }
  
  public Signature visitChannelSetPara(ChannelSetPara term)
  {
    // CircusParagraph ::= chanset N == CSExpression
    
    Name csName = term.getName();
    ZNameList genParams = term.getZGenFormals();
    ChannelSet cs = term.getChannelSet();
    
    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();
    
    //add the generic parameter names to the type env
    //this already checks if names are repeated.
    addGenParamTypes(genParams);
    
    // check this channel set
    ChannelSetType csType = (ChannelSetType)cs.accept(exprChecker());
    
    // create signature with the declared name
    // TODO: CHECK: Should it be a power type (i.e. factory().createPowerType(csType))?
    NameTypePair pair = factory().createNameTypePair(csName, csType);
    Signature result = factory().createSignature(pair);
    
    typeEnv().exitScope();
    
    addSignatureAnn(term, result);
    
    return result;
  }
  
  public Signature visitProcessPara(ProcessPara term)
  {
    // CircusParagraph ::= ProcessDeclaration
    // ProcessDeclaration ::= process N \defs ProcessDefinition
    // ProcessDeclaration ::= process N[N+] \defs ProcessDefinition
    
    Name pName = term.getName();
    ZNameList pGenFormals = term.getZGenFormals();
    CircusProcess process = term.getCircusProcess();
    
    // set current process name being checked.
    // this opens a process para scope, which is cleared at the end.
    // ActionPara can only be checked within an opened process para scope.
    Name old = setCurrentProcessName(pName);
    if (old != null)
    {
      Object[] params = { pName, old };
      error(term, ErrorMessage.NESTED_PROCESSPARA_SCOPE, params);
    } 
    
    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();
    
    //for keeping actions and process state
    localCircTypeEnv().enterScope();
    
    //add the generic parameter names to the type env
    addGenParamTypes(pGenFormals);
    
    // checks the process: everything is ready, but the process name.
    ProcessSignature sigProc = process.accept(processChecker());
    sigProc.setProcessName(pName);
    
    
    // pega os canais usados pelo processo e adiciona os possíveis canais implicitos
    List<NameTypePair> usedChans = localCircTypeEnv().getUsedChans();
    
    //TODO: add ZExprList getUsedChans(), where the result is a RefExpr of the
    //      (possibly generic instantiated) channel name. That means changing
    //      Circus.xsd
    //addImplicitChans(usedChans);
    //getProcessInfo(nameProc).setUsedChans(usedChans);
    
    // checks mutually recursive calls.
    // Manuela: the Circus type rules do not treat this.
    postActionCallCheck();
    
    // close environment scopes.
    localCircTypeEnv().exitScope();
    typeEnv().exitScope();
    
    // clears the process para scope.
    old = setCurrentProcessName(null);
    assert old == pName : "Invalid process para scoping for " + pName;
    
    // create the process type with corresponding signature.
    ProcessType procType = factory().createProcessType(sigProc);
    NameTypePair pair = factory().createNameTypePair(pName, procType);
    Signature result = factory().createSignature(factorry().list(pair));
    
    addSignatureAnn(term, result);
    
    return result;
  }
  
  // ok - verificado em 25/09/2005 às 10:29
  public Signature visitActionPara(ActionPara term)
  {
    // PParagraph ::= N \defs ActionDefinition
    
    // retrieve the paragraph structure
    Name aName = term.getName();
    CircusAction action = term.getCircusAction();
    
    // check process paragraph scope.
    checkProcessParaScope("action paragraph", aName);
    
    // check if name has been previously declared (?)
    // TODO: CHECK: this should be done at a kind of checkParaList for BasicProcesses.
    if(!isNewDef(aName))
    {
      Object [] params = {getCurrentProcessName(), aName};
      error(term, ErrorMessage.REDECLARED_DEF, params);
    }
    
    setCurrentAction(aName);
    
    // TODO: CHECK: done by PROCESS CHECKER?
    if(!localCircTypeEnv().addAction(actionName))
    {
      Object [] params = {actionName.getWord(), assertZDeclName(currentProcess()).getWord()};
      error(term, ErrorMessage.REDECLARED_ACTION_NAME, params);
    }
        
    typeEnv().enterScope();
    
    ActionSignature aSig = action.accept(actionChecker());
    aSig.setActionName(aName);
    
    typeEnv().exitScope();
    
    ActionType actionType = factory().createActionType(aSig);    
    NameTypePair pair = factory().createNameTypePair(actionName, actionType);
    Signature result = factory().createSignature(pair);
    
    // adiciona a ação no escopo do processo
    // TODO: CHECK: done by PROCESS CHECKER?
    //typeEnv().add(allPairs);
    
    //seta o tipo da ação no ambiente local. Impostante essa informação para postCheck
    localCircTypeEnv().setActionType(aName, actionType);
        
    addSignatureAnn(term, result);
    
    return result;
  }
  
  // PParagraph ::= nameset N == NSExpression
  //ok - verificado em 25/09/2005 às 10:30
  public Signature visitNameSetPara(NameSetPara term)
  {
    
    // retrieve the paragraph structure
    Name nsName = term.getName();
    NameSet ns = term.getNameSet();
    
    // check process paragraph scope.
    checkProcessParaScope("name set paragraph", nsName);
        
    Type2 nsType = ns.accept(exprChecker());
    
    //TODO: CHECK: is this really needed here? Or shoulbe be trated at checkParaList in ProcessChecker?
    if (!localCircTypeEnv().addNameSet(name))
    {
      Object [] params = {name.getWord()};
      error(term, ErrorMessage.REDECLARED_NAMESET_NAME, params);
    }
    
    // check if name has been previously declared (?)
    // TODO: CHECK: this should be done at a kind of checkParaList for BasicProcesses.
    if(!isNewDef(nsName))
    {
      Object [] params = {getCurrentProcessName(), nsName};
      error(term, ErrorMessage.REDECLARED_DEF, params);
    }

    NameTypePair pair = factory().createNameTypePair(nsName, nsType);
    Signature result = factory().createSignature(pair);
        
    // adiciona o conjunto de nomes no escopo do processo
    //typeEnv().add(pair);
    
    addSignatureAnn(term, result);
    
    return result;
  }
  
  public Signature visitTransformerPara(TransformerPara term)
  {
    UResult unify = term.getTransformerPred().accept(predChecker());
        
    // if not unifiable, this should be a UnknownType.
    Type2 type = getType2FromAnns(term);
    
    NameTypePair pair = factory().createNameTypePair(term.getName(), type);
    Signature result = factory().createSignature(pair);
    
    addSignatureAnn(term, result);
    
    return result;
  }
  
  /* TODO: 
   * Método auxiliar que adiciona os canais implicitos passados como parâmetro
   * no ambiente global, caso tais canais já não tenham sido declarados com
   * mesmo nome e tipos diferentes.
   * @param chans  a lista de canais implícitos a adicionar no ambiente
   */
  private void addImplicitChans(List<NameTypePair> chans)
  {
    for(NameTypePair chan : chans)
    {
      ZDeclName chanName = chan.getZDeclName();
      Type chanType = chan.getType();
      
      Type type = sectTypeEnv().getType(factory().createZRefName(chanName));
      if (sectTypeEnv().add(chanName, chanType) != null)
      {
        if (unify(unwrapType(type), unwrapType(chanType)) != SUCC)
        {
          // muitas vezes, porcausa da instanciação, o tipo de um canal genérico
          // passa a ser diferente.
          if(!isGenericChannel(chanName))
          {
            Object [] params = {assertZDeclName(currentProcess()).getWord(), chanName.getWord()};
            error(chanName, ErrorMessage.REDECLARED_GLOBAL_NAME_WITH_DIFF_TYPE, params);
            break;
          }
        }
        else
        {
          if(!isChannel(chanName))
          {
            Object [] params = {chanName.getWord()};
            error(chanName, ErrorMessage.REDECLARED_GLOBAL_NAME, params);
            break;
          }
        }
      }
      else
      {
        List<DeclName> genericImplicitChans = localCircTypeEnv().getGenericImplicitChans();
        if(genericImplicitChans.contains(chanName))
        {
          // E OS PARAMETROS ??
          addGenChannel(chanName, chanType, null);
        }
        else
        {
          addChannel(chanName, chanType);
        }
      }
    }
  }    
}
