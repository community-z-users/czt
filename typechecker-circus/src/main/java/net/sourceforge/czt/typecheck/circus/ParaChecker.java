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
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.TransformerParaVisitor;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;


/**
 * <p>
 * This visitor adds signature annotations to the paragraphs being checked.
 * That is, if no signature annotation is present, one is added. If one is present
 * and contains variable types, those variable types are updated with the new one.
 * Otherwise, if there are no variable types on an old signature, it is just overridden
 * with the updated signature. 
 * </p>
 * <p>
 * Clash of global name clashing is caught at
 * #z.Checker.checkParaList, which is called within #z.SpecChecker.visitZParaList.
 * At that time, global names are added to the sectTypeEnv() environment.
 * </p>
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
  TransformerParaVisitor<Signature>
{   
  /**
   * Flag to control whether the visitTerm is for a paragraph within or outside a process.  
   */
  private boolean isCheckingProcessZPara_;
  
  /**
   * Transformer paragraph name.
   */
  private final ZName transformerName_;
  
  /**
   * Transformer paragraph (spurious) type.
   */
  private Type2 transformerType_;

  
  /**
   * Reference to a Z paragraph checker for checking Z paragraphs
   */
  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;
  
  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);    
    isCheckingProcessZPara_ = false;
    zParaChecker_ = new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);    
    transformerName_ = factory().createTransformerName();
    transformerType_ = null;
  }  
  
  /**
   * Returns the synchronisation type for channels. The first time this type is 
   * looked up, the circus_prelude section must be visible.
   * 
   * @return
   */
  protected Type2 transformerType()
  {
    if (transformerType_ == null)
    {
      transformerType_ = checkUnificationSpecialType(transformerName_, CircusUtils.TRANSFORMER_TYPE);    
      // adds type annotation to these circus expressions 
      CircusUtils.TRANSFORMER_EXPR.accept(exprChecker());              
    }
    return transformerType_;
  }
  
  /**
   * This flag controls whether or not the general {@link #visitTerm(Term)}
   * method is checking a Z paragraph within the current process, or a 
   * Z paragraph in the global (section) scope.
   * @param val flag to set 
   */
  protected void setCheckingProcessZPara(boolean val)
  {
    isCheckingProcessZPara_ = val;
  }
    
  /**
   * For all other paragraph terms, use the standard Z typechecking rules 
   * within the checking environment for Circus. Note this is slightly 
   * different from top-level Z paragraph within a process. For those,
   * we need to take into account the process scoping rules, hence we use
   * a ProcessParaChecker. For instance, the SchText for the process state
   * is handled in there, and not here.
   *
   *@law C.18.3, C.18.4
   */
  @Override
  public Signature visitTerm(Term term)
  {
    // TODO: do something with isCheckingProcessZPara_ if needed.
    return term.accept(zParaChecker_);
  }
  
  /**
   * Type checks all ChannelDecl within the given ChannelPara using
   * the circus.DeclChecker, and then adds the resulting signature as
   * an annotation within the given term.
   *
   *@law C.3.3
   */
  @Override
  public Signature visitChannelPara(ChannelPara term)
  {
    // CircusParagraph ::= channel CDeclaration
       
    // visit all ChannelDecl within the ZDeclList of term
    // this uses the quite elegant (yet intricated) typechecker architecture
    // to use: z.DeclChecker.visitZDeclList(), and circus.DeclChecker.visitChannelDecl().
    //
    // \Gamma \rhd cd : CDeclaration    
    List<NameTypePair> pairs = term.getZDeclList().accept(declChecker());
    
    // check for duplicates within the ChannelPara scope.
    checkForDuplicates(pairs, null);
    
    //create the signature for this paragraph and add it as an annotation
    Signature signature = factory().createSignature(pairs);
    
    //creates a new, overrides existing, or updates variable signatures.
    addSignatureAnn(term, signature);
    
    return signature;
  }
  
  /**
   * <p>
   * First, it extracts the channel set name and declaration
   * from the given paragraph, where the (possibly empty) generic
   * formals are added into a new typing scope. 
   * </p>
   * <p>
   * Next, the channel set
   * declaration is checked with the ExprChecker. Note this is a slight
   * discrepancy in the Circus AST: ChannelSet is a subclass of Term that
   * contains an expression, which can either be a general Z expression or
   * a channel set display (i.e. BasicChannelSetExpr). 
   * </p>
   * <p>
   * Finally, the resulting
   * channelset type is wrapped up as a power type and returned as a signature
   * fromthe channel set name to this power type.
   * </p>
   *
   *@law C.3.2
   */
  @Override
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
    
    // n \notin \Gamma.defNames is checked by checkParaList() at the SpecChecker.
    
    // check this channel set
    // // \Gamma \rhd cs : CSExpression
    ChannelSetType csType = (ChannelSetType)cs.accept(exprChecker());
    csType.setName(csName);
    
    // create signature with the declared name
    // like other set types, it is wrapped within a power type
    PowerType pType = factory().createPowerType(csType);
    NameTypePair pair = factory().createNameTypePair(csName, pType);
    Signature result = factory().createSignature(pair);
    
    // add channel set power type to ChannelSet
    addTypeAnn(term.getChannelSet(), pType);
    // add signature to ChannelSetPara
    addSignatureAnn(term, result);   
    
    
    typeEnv().exitScope();
    
    return result;
  }
  
  /**
   * <p>
   * First, it extracts the process name and declaration
   * from the given paragraph, where the (possibly empty) generic
   * formals are added into a new typing scope. As nested processes
   * are not allowed, a check for current scopping is also made, where
   * the current process name being typechecked is remembered. Since we
   * also have basic (i.e., locally) defined processes, a local type 
   * environment is also used to track used channels, implicit channels,
   * and state information. 
   * </p>
   * <p>
   * Next, the process declaration is checked with the ProcessChecker,
   * where it returns a ProcessSignature containing all the collected 
   * information for the process. Process subclasses have different 
   * structures (i.e., global processes have a CircusProcessSignature, 
   * for what basic - local - processes have a BasicProcessSignature).
   * After typechecking the process declaration, we also need to update
   * the ProcessSignature with the process name and used channels, which
   * are NOT updated by the ProcessChecker.
   * </p>
   * <p>
   * After that, (possibly declared) implicit channels are added. Those
   * arise through IndexedProcesses, which can be either directly declared,
   * declared on-the-fly, or being renamed. This accounts for the 
   * MSc B.35, B.40, B.41 functions. Moreover, postcheck over the local
   * typing environment is performed to resolve mutual recursion.
   * </p>
   * <p>
   * Finally, both local and global typing environments are popped,
   * the current process name scope is closed, and the resulting 
   * signature is wrapped up with the process name and its type, 
   * which is formed by the collected ProcessSignature.
   * </p>
   *
   *@law C.3.4, C.6.1--C.6.8(?) TODO: CHECK:
   */
  @Override
  public Signature visitProcessPara(ProcessPara term)
  {
    // CircusParagraph ::= ProcessDeclaration
    // ProcessDeclaration ::= process N \defs ProcessDefinition
    // ProcessDeclaration ::= process N[N+] \defs ProcessDefinition
    
    // Unpack the process paragraph
    Name pName = term.getName();
    ZNameList pGenFormals = term.getZGenFormals();
    CircusProcess process = term.getCircusProcess();
    
    // set current process name being checked.
    // this opens a process para scope, which is cleared at the end.
    // ActionPara can only be checked within an opened process para scope.
    Name old = setCurrentProcessName(pName);
    setCurrentProcess(process);
    if (old != null)
    {
      Object[] params = { pName, old };
      error(term, ErrorMessage.NESTED_PROCESSPARA_SCOPE, params);
    }
    
    //we enter a new variable scope for the generic parameters
    typeEnv().enterScope();
    
    //add the generic parameter names to the type env
    addGenParamTypes(pGenFormals);
    
    // checks the process: everything is ready, but the process name.
    ProcessSignature sigProc = process.accept(processChecker());
    sigProc.setProcessName(pName);    
    
    // TODO!
    // retrieve the used channels within this process (see MSc. B.33 FindCP)         
    //List<NameTypePair> usedChans = circusTypeEnv().getUsedChans();
    //Signature usedChanSig = factory().createSignature(usedChans);
    //sigProc.setUsedChannels(usedChanSig);    
    
    // calculate possibly implicit channels within the used ones
    //addImplicitChans(usedChans);       
    
    // close environment scopes.    
    typeEnv().exitScope();
    
    // clears the process para scope.
    old = setCurrentProcessName(null);
    assert old == pName : "Invalid process para scoping for " + pName;
    setCurrentProcess(null);
    
    // create the process type with corresponding signature.
    ProcessType procType = factory().createProcessType(sigProc);
    NameTypePair pair = factory().createNameTypePair(pName, procType);
    Signature result = factory().createSignature(factory().list(pair));
    
    // add process type to CircusProcess
    addTypeAnn(term.getCircusProcess(), procType);
    
    // add signature to ProcessPara
    addSignatureAnn(term, result);           
    
    return result;
  }
  
  @Override
  public Signature visitTransformerPara(TransformerPara term)
  { 
    // for transformer para, no need to put into context early, since
    // no reference to such names is possible. so let the checkForDuplicates
    // at the process level check it.
    
    UResult solved = term.getTransformerPred().accept(predChecker());
    
    if (solved.equals(UResult.PARTIAL))
    {
      term.getTransformerPred().accept(predChecker());
    }
    
    NameTypePair pair = factory().createNameTypePair(term.getName(), transformerType());
    Signature result = factory().createSignature(pair);
    
    // add transformer pred type to TransformerPred
    addTypeAnn(term.getTransformerPred(), transformerType());
    
    // add signature to TransformerPara
    addSignatureAnn(term, result);   
    
    return result;
  }
  
  /* TODO: 
   * Mtodo auxiliar que adiciona os canais implicitos passados como par�metro
   * no ambiente global, caso tais canais j no tenham sido declarados com
   * mesmo nome e tipos diferentes.
   * @param chans  a lista de canais implcitos a adicionar no ambiente
   */
  private void addImplicitChans(List<NameTypePair> chans)
  {
    assert false : "TODO";
//    
//    for(NameTypePair chan : chans)
//    {
//      ZDeclName chanName = chan.getZDeclName();
//      Type chanType = chan.getType();
//      
//      Type type = sectTypeEnv().getType(factory().createZRefName(chanName));
//      if (sectTypeEnv().add(chanName, chanType) != null)
//      {
//        if (unify(unwrapType(type), unwrapType(chanType)) != SUCC)
//        {
//          // muitas vezes, porcausa da instanciao, o tipo de um canal genrico
//          // passa a ser diferente.
//          if(!isGenericChannel(chanName))
//          {
//            Object [] params = {assertZDeclName(currentProcess()).getWord(), chanName.getWord()};
//            error(chanName, ErrorMessage.REDECLARED_GLOBAL_NAME_WITH_DIFF_TYPE, params);
//            break;
//          }
//        }
//        else
//        {
//          if(!isChannel(chanName))
//          {
//            Object [] params = {chanName.getWord()};
//            error(chanName, ErrorMessage.REDECLARED_GLOBAL_NAME, params);
//            break;
//          }
//        }
//      }
//      else
//      {
//        List<DeclName> genericImplicitChans = localCircTypeEnv().getGenericImplicitChans();
//        if(genericImplicitChans.contains(chanName))
//        {
//          // E OS PARAMETROS ??
//          addGenChannel(chanName, chanType, null);
//        }
//        else
//        {
//          addChannel(chanName, chanType);
//        }
//      }
//    }
  }    
}
