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
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;


/**
 * TODO: CHECK? processParaChecker().addContext(type); ??
 *
 * @author leo
 */
public class ProcessParaChecker extends Checker<Signature>
  implements ActionParaVisitor<Signature>, // C.10.2, C.11.1, C.11.2
             NameSetParaVisitor<Signature> // C.10.3
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
        
    List<NameTypePair> pairs = result.getNameTypePair();
    for (NameTypePair pair : pairs)
    {
      //if the name already exists globally, raise an error
      Name name = pair.getName();      
      Type type = getLocalType(name);
      
      // if the type is known for this name at the process's global scope,
      // then we have duplicated declaration. TODO: check this with a test case.
      if (!(type instanceof UnknownType))
      {        
        Object [] params = { name, getConcreteSyntaxSymbol(term), getCurrentProcessName() };
        error(term, ErrorMessage.REDECLARED_DEF, params);
      }
    }      
    
    // add it to the process scope early
    typeEnv().add(pairs);    
    
    // added by ParaChecker
    // addSignatureAnn(term, result);
    
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
   * @law C.10.2, C.11.1, C.11.2
   */
  @Override
  public Signature visitActionPara(ActionPara term)
  { 
    // reset the visit count - this is important to make sure 
    // parameterised mu actions do not appear in inner processes.
    resetActionCheckerVisitCount();
    
    // check the inner action - also used in MuAction
    // it also checks for duplicate names.
    ActionSignature aSig = checkActionDecl(term.getName(), term.getCircusAction(), term);
    
    // for parameterised mu actions, change the signature so that calls to the 
    // action paragraph name require the formal parameters from the parameterised mu action
    if ((term.getCircusAction() instanceof MuAction) &&
        ((MuAction)term.getCircusAction()).isParameterised())
    {
      Type2 type = getType2FromAnns(term.getCircusAction());
      assert type instanceof ActionType : "cannot retrieve action type for mu action in action paragraph " + term.getName();
      
      // "export" the mu action formal parameters to the action paragraph being declared
      // and check that is doesn't have parameters already - which should never happen.      
      if (!aSig.getFormalParams().getNameTypePair().isEmpty())
      {
        Object[] params = { getCurrentProcessName(), term.getName() };
        error(term, ErrorMessage.NESTED_FORMAL_PARAMS_IN_ACTION, params);
      }
      aSig.setFormalParams(((ActionType)type).getActionSignature().getFormalParams());      
    }
    
    // wraps up the action type
    ActionType actionType = factory().createActionType(aSig);    
    Signature result = wrapTypeAndAddAnn(term.getName(), actionType, term);    
        
    return result;
  }
  
  protected Signature wrapTypeAndAddAnn(Name declName, Type type, Para term)
  {
    Signature result = super.wrapTypeAndAddAnn(declName, type, term);

    // put this paragraph into the BasicProcess scope early,
    // so that some forms of mutual recursion may be resolved directly.
    // i.e., allow the name to be into scope at early stage?
    
    // TODO: CHECK: what if we get duplicated names?
    typeEnv().add(result.getNameTypePair());

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
   * @law C.10.3
   */
  @Override
  public Signature visitNameSetPara(NameSetPara term)
  {     
    // retrieve the paragraph structure    
    Name nsName = term.getName();
    NameSet ns = term.getNameSet();    
        
    // check process paragraph scope.
    checkProcessParaScope(term, nsName);
    
    // TODO: CHECK: if this redeclared business is needed
    Type type = getLocalType(nsName);
    if (type instanceof UnknownType)
    {
      // set current name set being checked.      
      Name old = setCurrentNameSetName(nsName);
      NameSet oldNameSet = setCurrentNameSet(ns);      
      if (old != null)
      {
        Object[] params = { getCurrentProcessName(), nsName, old };
        error(term, ErrorMessage.NESTED_NAMESETPARA_SCOPE, params);
      }
            
      List<Object> errorParams = factory().list();
      errorParams.add(getCurrentProcessName());
      errorParams.add("name set");
      errorParams.add(getCurrentNameSetName());                
      NameSetType nsType = typeCheckNameSet(ns, errorParams);
      
      PowerType pType = factory().createPowerType(GlobalDefs.unwrapType(nsType));
      
      // TODO: check if this is needed. I think so because processes might contain generic
      //       types in its state from the process generics.
      type = addGenerics(pType);

      // restors the process para scope.
      old = setCurrentNameSetName(old);
      oldNameSet = setCurrentNameSet(oldNameSet);
      assert old == nsName && 
             oldNameSet == ns : "Invalid name set para scoping for " + nsName;
    }
    else
    {
      Object [] params = { nsName, getConcreteSyntaxSymbol(term), getCurrentProcessName() };
      error(term, ErrorMessage.REDECLARED_DEF, params);      
    }    
    Signature result = wrapTypeAndAddAnn(nsName, type, term);
    
    return result;
  }  
}
