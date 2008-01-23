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
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.circus.impl.ChannelInfo;
import net.sourceforge.czt.typecheck.circus.impl.ProcessInfo;
import net.sourceforge.czt.typecheck.circus.util.CarrierSet;
import net.sourceforge.czt.typecheck.circus.util.GenChannelDeclChecker;
import net.sourceforge.czt.typecheck.circus.util.ChannelsUsedChecker;
import net.sourceforge.czt.typecheck.circus.util.TypeEnv;
import net.sourceforge.czt.typecheck.circus.util.UnificationEnv;
import net.sourceforge.czt.typecheck.z.SchTextChecker;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.ZParaList;


/**
 *
 * @author Leo Freitas, Manuela Xavier
 */
public class TypeChecker 
  extends net.sourceforge.czt.typecheck.z.TypeChecker
{
  /**
   * Controls whether to create a LetVar action for place where 
   * implicit declarations or declared variable types are needed.
   */ 
  protected boolean shouldCreateLetVars_ = false;
 
  /* NOTE: All names here allow jokers! */
  
  /** 
   * The name of the current process being typechecked - null if we are 
   * not typechecking a process paragraph.
   */
  protected Name currentProcessName_;

  /**
   * The name of the current action being typechecked - null if we are
   * not typechecking a action paragraph.
   */
  protected Name currentActionName_;

  /**
   * The name of the current state process
   */
  protected Name stateName_;
    
  /** 
   * List of implicit processes. Implicit process should not be jokers (?)
   */
  protected ZParaList onTheFlyProcesses_;
  
//  /** 
//   * The declared channels. 
//   */
//  protected List<ChannelInfo> channels_;
//  
//  /** The chansets. */
//  protected NameList chansets_;
//  
//  // mu processes
//  protected NameList muProcesses_;
//  // mu actions 
//  protected NameList muActions_;
//  
//  protected NameList actions4PostCheck_;
  
  // flag for whether the delcarations being checked are for circus formal parameters
  protected boolean circusFormalParameters_ = false;
    
  //the visitors used to typechecker a Circus program
  protected Checker<Signature> signatureChecker_;
  protected Checker<ActionSignature> actionChecker_;
  protected Checker<ActionSignature> commandChecker_;
  protected Checker<List<NameTypePair>> commChecker_;
  protected Checker<ProcessSignature> processChecker_;
  protected Checker<Signature> processParaChecker_;
  // auxiliar visitor to typechecker a channel declaration
  protected Checker<Boolean> channelDeclChecker_;
  // auxiliar visitor to find used channels into a process
  protected Checker<NameList> channelsUsedChecker_;

  public TypeChecker(net.sourceforge.czt.typecheck.circus.impl.Factory factory,
                     SectionManager sectInfo)
  {
    this(factory, sectInfo, false);
  }

  public TypeChecker(net.sourceforge.czt.typecheck.circus.impl.Factory factory,
                     SectionManager sectInfo,
                     boolean useBeforeDecl)
  {
    // create all the checkers as default - for Z
    super(factory, sectInfo, useBeforeDecl);     
    
    // override the default creation with those for Circus.
    unificationEnv_ = new UnificationEnv(factory);
    carrierSet_ = new CarrierSet();
    
    // make sure specChecker is the first checker created     
    // this is important because it creates the "Synch" channel 
    // into the sectTypeEnv(), which is looked up by the 
    // CommunicationChecker constructor
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    schTextChecker_ = new SchTextChecker(this);
    postChecker_ = new PostChecker(this);                    
    signatureChecker_ = new SignatureChecker(this);
    processParaChecker_ = new ProcessParaChecker(this);
    
    actionChecker_ = new ActionChecker(this);
    commandChecker_ = new CommandChecker(this);
    commChecker_ = new CommunicationChecker(this);
    processChecker_ = new ProcessChecker(this);
    
    currentProcessName_ = null;
    currentActionName_ = null;
    stateName_ = null;
    onTheFlyProcesses_ = null;
    circusFormalParameters_ = false;
    shouldCreateLetVars_ = false;

    channels_ = new ArrayList<ChannelInfo>();
    
    chansets_ = getFactory().createZNameList();    
    muProcesses_ = getFactory().createZNameList();    
    muActions_ = getFactory().createZNameList();    
    actions4PostCheck_ = getFactory().createZNameList();    
    
    // auxiliar visitors
    channelDeclChecker_ = new GenChannelDeclChecker(this);
    channelsUsedChecker_ = new ChannelsUsedChecker(this);
    
    // override default type environment classes to be 
    // a Circus type environment, which allows extra info for checkers.
    typeEnv_ = new TypeEnv(getFactory());
    pending_ = new TypeEnv(getFactory());
  }  

  public net.sourceforge.czt.typecheck.circus.impl.Factory getFactory()
  {
    return (net.sourceforge.czt.typecheck.circus.impl.Factory) super.getFactory();
  }
  
  public boolean setCreateLetVar(boolean val)
  {
    boolean result = shouldCreateLetVars_;
    shouldCreateLetVars_ = val;
    return result;
  }

  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    super.setPreamble(sectName, sectInfo);
  }    
}