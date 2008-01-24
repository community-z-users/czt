/*
 * ProcessParaChecker.java
 *
 * Created on 16 January 2008, 16:09
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.typecheck.circus;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;


/**
 * TODO: CHECK? processParaChecker().addContext(type); ??
 *
 * @author leo
 */
public class ProcessParaChecker extends Checker<Signature>
  implements ActionParaVisitor<Signature>,
             NameSetParaVisitor<Signature>
{
  public ProcessParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);        
  }
  
  /**
   * For a general terms (i.e. all other Para subclasses), we just apply Z typechecking.
   * This includes given sets, axiomatic and schema boxes, horizontal definitions,
   * conjectures, and so forth. Note this also includes TransformerPara, which can
   * appear both within and outside processes.
   * 
   *@law C.10.1
   */
  @Override
  public Signature visitTerm(Term term)
  {
    // check within process scope.
    checkProcessParaScope(term, null);
    
    ((ParaChecker)paraChecker()).setCheckingProcessZPara(true);
    Signature result = term.accept(paraChecker());
    ((ParaChecker)paraChecker()).setCheckingProcessZPara(false);
    
    return result;
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
   * 
   * @law C.10.2
   */
  @Override
  public Signature visitActionPara(ActionPara term)
  {    
    // retrieve the paragraph structure
    ZName aName = term.getZName();
    CircusAction action = term.getCircusAction();
       
    // check process paragraph scope.
    checkProcessParaScope(term, aName);
    
    ActionSignature aSig;
    
    // TODO: CHECK: not sure if this is a good idea because it may annotate
    //              aName with an UnderclaredAnn ? Not if directly from typeEnv()
    //              rather than Checker.getType(aName);    
    Type type = typeEnv().getType(aName);
    if (type instanceof UnknownType)
    {
      // set current action name being checked.
      // this opens a action para scope, which is cleared at the end.
      // Actions can only be checked within an opened action para scope.
      Name old = setCurrentActionName(aName);
      setCurrentAction(action);
      if (old != null)
      {
        Object[] params = { getCurrentProcessName(), aName, old };
        error(term, ErrorMessage.NESTED_ACTIONPARA_SCOPE, params);
      }

      // enter scope for local variables within an action paragraph    
      // since these are local to the process, they must be within 
      // the type environment.
      typeEnv().enterScope();

      // check the declared action updating its name on the returned action signature
      aSig = action.accept(actionChecker());
      assert ZUtils.namesEqual(aSig.getActionName(), aName) : 
        "action signature built outside proper action para scope: found: " + 
        aSig.getActionName() + "; expected: " + aName;

      // closes local vars and formal parameters scope
      typeEnv().exitScope();

      // clears the process para scope.
      old = setCurrentActionName(null);
      assert old == aName : "Invalid action para scoping for " + aName;
      setCurrentAction(null);
      
    }
    else
    {
      aSig = factory().createEmptyActionSignature();
      aSig.setActionName(aName);
      Object [] params = {aName, "action paragraph", getCurrentProcessName() };
      error(term, ErrorMessage.REDECLARED_DEF, params);      
    }
    
    // wraps up the action type
    ActionType actionType = factory().createActionType(aSig);    
    NameTypePair pair = factory().createNameTypePair(aName, actionType);
    Signature result = factory().createSignature(pair);
    
    // add action type to CircusAction
    addTypeAnn(term.getCircusAction(), actionType);
    // add signature to ActionPara
    addSignatureAnn(term, result);
    
    // put this paragraph into the BasicProcess scope early,
    // so that some forms of mutual recursion may be resolved directly.
    // i.e., allow the name to be into scope at early stage?
    // TODO: CHECK: what if we get duplicated names?
    typeEnv().add(pair);
    
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
   * 
   * @law C.10.3
   */
  @Override
  public Signature visitNameSetPara(NameSetPara term)
  {    
    // retrieve the paragraph structure
    ZName nsName = term.getZName();
    NameSet ns = term.getNameSet();
    
    // check process paragraph scope.
    checkProcessParaScope(term, nsName);
    
    Type type = typeEnv().getType(nsName);
    if (type instanceof UnknownType)
    {
      type = ns.accept(exprChecker());      
      if (type instanceof NameSetType)
      {
        // is this name on the type really needed/useful? TODO: CHECK:
        // maybe for name set references in parallel constructs?
        ((NameSetType)type).setName(nsName);        
      }
    }
    else
    {
      Object [] params = { nsName, "name set paragraph", getCurrentProcessName() };
      error(term, ErrorMessage.REDECLARED_DEF, params);
    }
    assert (type instanceof NameSetType || type instanceof UnknownType);
    
    PowerType pType = factory().createPowerType(GlobalDefs.unwrapType(type));
    NameTypePair pair = factory().createNameTypePair(nsName, pType);
    Signature result = factory().createSignature(pair);
            
    // add nameset power type to NameSet
    addTypeAnn(term.getNameSet(), pType);
    // add signature to NameSetPara
    addSignatureAnn(term, result);   
    
    // add it to the process scope early
    typeEnv().add(pair);
    
    return result;
  }
}
