/*
 * TypeEnv.java
 *
 * Created on 17 de Junho de 2005, 17:36
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.typecheck.circus.util;

import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.typecheck.circus.impl.ActionInfo;
import net.sourceforge.czt.typecheck.circus.impl.Factory;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.ZName;

/**
 * A local type environment is used to calculate type information local to
 * a process. It was used in a previous implementation to partially represent 
 * the Gama environment mentioned in Manuela's MSc (p.37). 
 *
 * In this implementation, we harmonise those ideas within the CZT typechecking
 * framework. Essentially, everything is a list of (Name, Type) pairs, where 
 * really extra information is added accordingly. That is, in the original work
 * one could have, say, a set of declared name sets but no type information for them.
 * In here, we do, and the type information will be the signature representing 
 * the declaring types of the variables within the nameset. For name sets as 
 * ApplExr, we add an empty signature (i.e. it is not possible for the typechecker
 * to deduce the whole space of names such an abstraction would represent).
 * 
 * @author Leo Freitas 
 */
public class LocalTypeEnv
  extends net.sourceforge.czt.typecheck.z.util.TypeEnv
{
  /** The list of used channels */
  protected Stack<List<NameTypePair>> usedChans_;
  
  /** A pilha dos canais implicitos e genéricos */
  protected Stack<List<NameTypePair>> genericImplicitChans_;
 
  /** Creates a new instance of LocalTypeEnv */
  public LocalTypeEnv(net.sourceforge.czt.typecheck.circus.impl.Factory circusFactory/*, TypeEnv globalEnv*/)
  {    
    super(circusFactory/*, globalEnv*/);
    usedChans_ = new Stack<List<NameTypePair>>();
    genericImplicitChans_ = new Stack<List<NameTypePair>>();
  }  
 
  /**
   * 
   */
  public net.sourceforge.czt.typecheck.circus.impl.Factory getFactory()
  {
    return (net.sourceforge.czt.typecheck.circus.impl.Factory)factory_;
  }
  
  public void enterScope()
  {    
    List<NameTypePair> usedChans = getFactory().list();    
    usedChans_.push(usedChans);
    List<NameTypePair> genericImplicitChans = getFactory().list();
    genericImplicitChans_.push(genericImplicitChans);    
  }

  public void exitScope()
  {    
    usedChans_.pop();
    genericImplicitChans_.pop();
  }
  
  /** 
   * General method that checks whether the given name is typed with
   * the expected type Type class. If the type info stack does not have
   * type information for the given name, the result is obviously false
   * regardless of the expected class.
   */
  protected boolean isTypedAsExpected(ZName name, Class<? extends Type> expected)
  {
    assert name != null && expected != null;
    
    // NOTE: Originally, Manuela used name comparison (possibly) without 
    //       considering strokes (see GlobalDefs.compareNames). This does
    //       not seem to make much sense and it wasn't well motivated. 
    //       In any case, TypeEnv.getType uses getX, which uses "namesEqual"
    //       method that does the right name comparison.
    
    // retrieve type information for given name
    Type type = getType(name);        
    
    // checks whether it is non-null and of the expected type    
    return expected.isInstance(type);
  }
  
  /** A name is a nameset if it has NameSetType */
  public boolean isNameSet(ZName name){    
    return isTypedAsExpected(name, NameSetType.class);
  }
  
  /** A name is an action if it has ActionType */
  public boolean isAction(ZName name){
    return isTypedAsExpected(name, ActionType.class);    
  }  
  
  /**
   * A name is a parameterised action if it has ActionType
   * and the formal parameters signature within the action 
   * signature is not empty.
   */
  public boolean isParamAction(ZName name) {    
    Type type = getType(name);
    boolean result = type instanceof ActionType;
    if (result)
    {      
      ActionType atype = (ActionType)type;
      result = !atype.getActionSignature().getFormalParams().getNameTypePair().isEmpty();
    }    
    return result;
  }
  
  protected ZStrokeList getCircusStrokeListForStateVar()
  {
      ZStrokeList zsl = getFactory().getZFactory().createZStrokeList();
      zsl.add(getFactory().createNextStroke());
      zsl.add(getFactory().createInStroke());
      zsl.add(getFactory().createOutStroke());
      return zsl;
  }
   
  /**
   * Adds the given name type pair into the current type information scope,
   * provided the name hasn't been declared in the current scope yet. It also
   * adds stroked variations of the given name according to the strokes 
   * returned by #getCircusStrokeListForStateVar (i.e. ', ?, !).
   * 
   * In case there is naming conflict, the result is null. 
   * Otherwise, it contains the list of names that generated the conflict.
   * (i.e. "result = null || !result.isEmpty()" is part of the postcondition)
   */
  public List<ZName> addStateVar(NameTypePair pair)
  {        
    ZName varName = pair.getZName();    
    Type varType = pair.getType();      
    
    List<ZName> existingNames = getFactory().list();
    NameTypePair existing = getPair(varName);
    
    //if not already declared, add this declaration to the environment
    //together with its getCircusStrokeListForStateVar()+1 (=4) variations    
    if (existing == null)
    { 
      // add the original variable name to the scope, say "v"
      List<NameTypePair> stateVars = getFactory().list();
      stateVars.add(pair);      
      
      ZStrokeList zsl = getCircusStrokeListForStateVar();
      for(Stroke stroke : zsl)
      { 
        // create a stroked version " v'/v?/v! " with same ID as "v" (just like Z tc does) in getDeltaXiType(...)
        ZName strokedName = getFactory().createZName(varName, true);      
        strokedName.getZStrokeList().add(stroke);
        NameTypePair strokedPair = getFactory().createNameTypePair(strokedName, varType);
        
        // check whether the pair could have been created previously (very unlikely, but...)
        existing = getPair(strokedName);
        // if not, add it to the stateVars
        if (existing == null)
        {
          stateVars.add(strokedPair);
        }
        // otherwise add the name for a complete error message
        else
        {
          existingNames.add(varName);
          existing.setType(varType);      
        }
      } 
      
      // if no new variable already existed, then add then all to the type environment
      if (existing == null)
      {
        assert (stateVars.size() == zsl.size() + 1) :
          "State variable declarations must add " + (zsl.size() + 1) + 
          " variables in total.";
        
        // add all four variations to the type environment.
        add(stateVars);
      }
    }
    //otherwise, overwrite the existing declaration, and note that
    //this declaration is a duplicate (i.e. result = false)
    else
    {      
      existingNames.add(varName);
      existing.setType(varType);      
    } 
    
    // if there were some duplicate pair, raise the error
    if (/*existing != null ||*/ !existingNames.isEmpty())
    {
      assert existing != null;
      //Object [] params = {existingNames.toString()};
      //error(term, ErrorMessage.REDECLARED_STATEVAR_NAME, params);
      return existingNames;
    }
    else
    {
      return null;
    }
  }
  
  public void addUsedChans(List<NameTypePair> chans) {
    List<NameTypePair> usedChans = usedChans_.peek();
    for(NameTypePair pair : chans) {
      if(!usedChans.contains(pair)) {
        usedChans.add(pair);
      }
    }
  }

  public void addGenericImplicitChan(Name name) {
    List<NameTypePair> genericChans = genericImplicitChans_.peek();
    for(NameTypePair pair : chans) {
      if(!genericChans.contains(pair)) {
        genericChans.add(pair);
      }
    }
    if(!genericChans.contains(name)) {
      //genericChans.add(name);
    }
  } 
}
