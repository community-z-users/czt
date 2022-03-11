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
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
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
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
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
 */
public class ParaChecker
  extends Checker<Signature>            // C.3.1, C.18.3, C.18.4 - with visitTerm(Term)
  implements  
  ChannelSetParaVisitor<Signature>,     // C.3.2
  ChannelParaVisitor<Signature>,        // C.3.3
  ProcessParaVisitor<Signature>,        // C.3.4, C.6.1, C.6.2, C.6.5. C.6.8
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
  
  protected boolean isCheckingProcessZPara()
  {
	  return isCheckingProcessZPara_;
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
      transformerType_ = checkUnificationSpecialType(transformerName_, factory().createTransformerType());    
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
   *@law C.3.1, C.18.3, C.18.4
   */
  @Override
  public Signature visitTerm(Term term)
  {
    // TODO: do something with isCheckingProcessZPara_ if needed.
    return term.accept(zParaChecker_);
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
    
    ZName csName = term.getZName();
    ZNameList genParams = term.getZGenFormals();
    ChannelSet cs = term.getChannelSet();    
        
    //pending().enterScope();
    
    //we enter a new variable scope for the generic parameters    
    typeEnv().enterScope();

    //add the generic parameter names to the type env
    //this already checks if names are repeated.
    addGenParamTypes(genParams);

    // n \notin \Gamma.defNames is checked by checkParaList() at the SpecChecker.

    // within the ChannelSetPara, it must be a declaration
    List<Object> params = factory().list();
    params.add("channel set");
    params.add(csName);
    
    Name old = setCurrentChannelSetName(csName);    
    setCurrentChannelSet(cs);    
    if (old != null)
    {
      Object[] nested = { csName, old };
      error(term, ErrorMessage.NESTED_PROCESSPARA_SCOPE, nested);
    }
    
    // check this channel set
    // // \Gamma \rhd cs : CSExpression
    ChannelSetType csType = typeCheckChannelSet(cs, params);

    // create signature with the declared name
    // like other set types, it is wrapped within a power type
    PowerType pType = factory().createPowerType(GlobalDefs.unwrapType(csType));
    
    Type gType = addGenerics(pType);
    
    
    Signature result = wrapTypeAndAddAnn(csName, gType, term);

    typeEnv().exitScope();    
    
    //pending().exitScope();
    
   // clears the channel set para scope.
    old = setCurrentChannelSetName(null);
    assert old == csName : "Invalid channel set para scoping for " + csName;
    setCurrentChannelSet(null);
        
    return result;
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
  
  List<ProcessType> pTypeList_ = new java.util.ArrayList<ProcessType>();
  
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
   * structures.
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
   *@law C.3.4, C.6.1, C.6.2, C.6.5. C.6.8
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
    
    ProcessSignature pSig = factory().createEmptyProcessSignature();
    pSig.setGenFormals(pGenFormals);
    //pSig.setProcessName(pName);
    
    // set current process name being checked.
    // this opens a process para scope, which is cleared at the end.    
    Name old = setCurrentProcessName(pName);
    //CircusProcess oldProcess = 
    	setCurrentProcess(process);
    //ProcessSignature oldSignature = 
    	processChecker().setCurrentProcessSignature(pSig);
    if (old != null)
    {
      Object[] params = { pName, old };
      error(term, ErrorMessage.NESTED_PROCESSPARA_SCOPE, params);
    }
    
    // allow room for generics within this global name
    //pending().enterScope();
    
    //we enter a new variable scope for the generic parameters    
    typeEnv().enterScope();
    
    //add the generic parameter names to the type env
    addGenParamTypes(pGenFormals);
    
    // checks the process: everything is ready, but the process name.
    @SuppressWarnings("unused")
	CircusCommunicationList commList = process.accept(processChecker());        
    
    // create the process type with corresponding signature.
    ProcessSignature currentSig = processChecker().getCurrentProcessSignature();
    currentSig.setProcessName(getCurrentProcessName());
    //currentSig = factory().deepCloneTerm(currentSig);

    // clears the process para scope.
    old = setCurrentProcessName(null);    
    setCurrentProcess(null);  
    processChecker().setCurrentProcessSignature(null);
    assert old == pName : "Invalid process para scoping for " + pName;
       
    ProcessType procType = factory().createProcessType(currentSig);    
    Type gProcType = addGenerics(procType);
    pTypeList_.add(procType);
    Signature result = wrapTypeAndAddAnn(pName, gProcType, term);
    
    // close environment scopes.    
    typeEnv().exitScope();
    
    //pending().exitScope();    

    return result;
  }  
  
  @Override
  public Signature visitTransformerPara(TransformerPara term)
  { 
    // for transformer para, no need to put into context early, since
    // no reference to such names is possible. so let the checkForDuplicates
    // at the process level check it.
    
    typeCheckPred(term, term.getTransformerPred());
        
    Signature result = wrapTypeAndAddAnn(term.getName(), transformerType(), term);
    
    // add transformer pred type to TransformerPred
    addTypeAnn(term.getName(), transformerType());
    addTypeAnn(term.getTransformerPred(), transformerType());
    
    // add signature to TransformerPara
    //addSignatureAnn(term, result);   
    
    return result;
  }
}
