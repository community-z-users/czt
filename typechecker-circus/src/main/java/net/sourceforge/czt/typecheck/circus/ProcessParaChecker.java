/*
 * ProcessParaChecker.java
 *
 * Created on 16 January 2008, 16:09
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.typecheck.circus;

import java.util.List;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;


/**
 * TODO: CHECK? processParaChecker().addContext(type); ??
 *
 * @author leo
 */
public class ProcessParaChecker extends Checker<Signature>
  implements ActionParaVisitor<Signature>,
             NameSetParaVisitor<Signature>
{  
  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;
  
  public ProcessParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);    
    zParaChecker_ =
      new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);
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
   * <p>
   * First, it extracts the action name and declaration
   * from the given paragraph. As actions are syntacticly 
   * allowed only within a basic process, we also check that
   * there is one into scope, and has not yet been declared in
   * the process scope. The current action name is stored, and
   * since since we need further scopping within the local environment 
   * for variables and action parameters declarations, the local type
   * environment is also expanded.
   * </p>
   * <p>
   * Next, the action declaration is checked with the ActionChecker,
   * where it returns an ActionSignature containing all the collected 
   * information for the action. Process subclasses have different 
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
   */
  public Signature visitActionPara(ActionPara term)
  {
    // PParagraph ::= N \defs ActionDefinition
    
    // retrieve the paragraph structure
    Name aName = term.getName();
    CircusAction action = term.getCircusAction();
    
    // check process paragraph scope.
    checkProcessParaScope("Action paragraph", aName);
    
    // check if name has been previously declared     
    if(!isLocalNameFresh(aName))
    {
      Object [] params = {aName, "action paragraph", getCurrentProcessName() };
      error(term, ErrorMessage.REDECLARED_DEF, params);      
    }    
    
    // sets the current action scope
    setCurrentAction(aName);
        
    // enter scope for local variables within an action paragraph    
    // since these are local to the process, they must be within 
    // the local type environment, rather than the global typeEnv().
    
    // TODO: DEBUG: Manuela's implementation used typeEnv(). 
    //              Since there was no proper type annotation added,
    //              or environment search done later, then this could
    //              have been irrelevant. Unless, local names were reused.
    //              
    //       ADD TEST: different actions within a basic process declaring same vars.
    //                 ex: A = var x: \nat @ c!x -> Skip (and same for B) within P
    //  
    //       ADD TEST: similar test but across different processes as well.
    localCircTypeEnv().enterScope();
    
    // check the declared action updating its name on the returned action signature
    ActionSignature aSig = action.accept(actionChecker());
    aSig.setActionName(aName);
    
    // TODO: CHECK: aSig.getFormalParams() could just be within getLocalVars(). add the qualification of the decl as an ann
    
    // retrieve the used channels within this action (see MSc. B.33 FindCP)         
    List<NameTypePair> usedChans = localCircTypeEnv().getUsedChans();
    Signature usedChanSig = factory().createSignature(usedChans);
    aSig.setUsedChannels(usedChanSig);      
    
    // closes local vars scope
    localCircTypeEnv().exitScope();
    
    // wraps up the action type
    ActionType actionType = factory().createActionType(aSig);    
    NameTypePair pair = factory().createNameTypePair(actionName, actionType);
    Signature result = factory().createSignature(pair);
        
    addSignatureAnn(term, result);
    
    return result;
  }
  
  /**
   * <p>
   * First, it extracts the name set name and declaration
   * from the given paragraph. As name sets are syntacticly 
   * allowed only within a basic process, we also check that
   * there is one into scope, and has not yet been declared in
   * the process scope. The current action name is stored, and
   * since since we need further scopping within the local environment 
   * for variables and action parameters declarations, the local type
   * environment is also expanded.
   * </p>
   * <p>
   * Next, the action declaration is checked with the ActionChecker,
   * where it returns an ActionSignature containing all the collected 
   * information for the action. Process subclasses have different 
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
   */
  public Signature visitNameSetPara(NameSetPara term)
  {
    
    // retrieve the paragraph structure
    Name nsName = term.getName();
    NameSet ns = term.getNameSet();
    
    // check process paragraph scope.
    checkProcessParaScope("Name set paragraph", nsName);
        
    localCircTypeEnv().enterScope();
    
    Type2 nsType = ns.accept(exprChecker());
       
    // check if name has been previously declared (?)
    // TODO: CHECK: this should be done at a kind of checkParaList for BasicProcesses.
    if(!isLocalNameFresh(nsName))
    {
      Object [] params = {aName, "name set paragraph", getCurrentProcessName() };
      error(term, ErrorMessage.REDECLARED_DEF, params);
    }

    NameTypePair pair = factory().createNameTypePair(nsName, nsType);
    Signature result = factory().createSignature(pair);
        
    // adiciona o conjunto de nomes no escopo do processo
    //typeEnv().add(pair);
    
    localCircTypeEnv().exitScope();
    
    addSignatureAnn(term, result);
    
    return result;
  }  
}
