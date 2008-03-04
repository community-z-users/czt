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

import java.util.Map;
import java.util.Stack;
import java.util.List;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.ZName;

/**
 * A type environment 
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
public class TypeEnv
  extends net.sourceforge.czt.typecheck.z.util.TypeEnv
{
  /** 
   * Used channels in the current scope, where the type in the pair is always 
   * a ChannelType. This information is used to build action/process signatures.
   * Also, the name is a key, for the name type pair (i.e. key names within the map 
   * are always the getName within the pair.
   */
  protected Stack<Map<ZName, NameTypePair>> usedChans_;
  
  /** 
   * A stack for implicit and/or generic channels.
   */
  protected Stack<Map<ZName, NameTypePair>> genericImplicitChans_;
 
  
  protected Stack<CircusCommunicationList> usedComm_;
  /**
   * Creates a new instance of TypeEnv
   */
  public TypeEnv(net.sourceforge.czt.typecheck.circus.impl.Factory circusFactory)
  {    
    super(circusFactory);
    usedChans_ = new Stack<Map<ZName, NameTypePair>>();
    genericImplicitChans_ = new Stack<Map<ZName, NameTypePair>>();
    usedComm_ = new Stack<CircusCommunicationList>();
  }
 
  /**
   * 
   */
  @Override
  public net.sourceforge.czt.typecheck.circus.impl.Factory getFactory()
  {
    return (net.sourceforge.czt.typecheck.circus.impl.Factory)factory_;
  }
  
  @Override
  public void enterScope()
  {    
    super.enterScope();
    Map<ZName, NameTypePair> usedChans = GlobalDefs.map();
    usedChans_.push(usedChans);
    Map<ZName, NameTypePair> genericImplicitChans = GlobalDefs.map();
    genericImplicitChans_.push(genericImplicitChans);        
    CircusCommunicationList commList = getFactory().getCircusFactory().createCircusCommunicationList();
    usedComm_.push(commList);
  }

  @Override
  public void exitScope()
  {    
    usedChans_.pop();
    genericImplicitChans_.pop();
    super.exitScope();
  }
   
  /**
   * Retrieve the used channels within the current scope (see MSc. B.33 FindCP(?))         
   */
  protected List<NameTypePair> getUsedChans()
  {
    assert !usedChans_.isEmpty() : "empty stack of used channels";
    List<NameTypePair> result = getFactory().list();
    result.addAll(usedChans_.peek().values());
    return result;
    
  }
  
  /**
   * Retrieve the used channels within the current scope (see MSc. B.33 FindCP(?))         
   */
  protected List<NameTypePair> getImplicitUsedChans()
  {
    assert !genericImplicitChans_.isEmpty() : "empty stack of implicitly used channels";
    List<NameTypePair> result = getFactory().list();
    result.addAll(genericImplicitChans_.peek().values());
    return result;
    
  }
  
  protected CircusCommunicationList getUsedCommunicationList()
  {
    assert !usedComm_.isEmpty() : "empty stack of used communications";
    CircusCommunicationList result = getFactory().getCircusFactory().createCircusCommunicationList();
    result.addAll(usedComm_.peek());
    return result;
  }
  
  /**
   * Add the channel as used within the current context only.
   */
  public void addUsedChannels(boolean implicit, NameTypePair... chans) {
    assert (implicit ? !genericImplicitChans_.isEmpty() : 
      !usedChans_.isEmpty()) : "empty stack of used channels";
    Map<ZName, NameTypePair> uc = implicit ? genericImplicitChans_.peek() : usedChans_.peek();
    for(NameTypePair pair : chans) {
      NameTypePair hasNTP = getX(pair.getZName(), uc);
      if (hasNTP == null)      
      {
        uc.put(pair.getZName(), pair);
      }      
    }
  }
  
   public void addUsedCommunication(Communication comm)
  {
    assert !usedComm_.isEmpty() : "empty stack of used communications";
    CircusCommunicationList ccl = usedComm_.peek();
    ccl.add(comm);        
  } 
}
