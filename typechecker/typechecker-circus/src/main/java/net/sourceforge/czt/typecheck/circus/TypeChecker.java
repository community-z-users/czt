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

import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbolVisitor;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.circus.util.CarrierSet;
import net.sourceforge.czt.typecheck.circus.util.UnificationEnv;
import net.sourceforge.czt.typecheck.z.SchTextChecker;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.ZParaList;


/**
 *
 * @author Leo Freitas
 */
public class TypeChecker 
  extends net.sourceforge.czt.typecheck.z.TypeChecker
  implements TypecheckPropertiesKeys
{
  /**
   * Controls whether to create a LetVar action for place where 
   * implicit declarations or declared variable types are needed.
   */ 
  protected boolean shouldCreateLetVars_ = PROP_TYPECHECK_CREATE_LETVAR_DEFAULT;
 
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
  
  protected Name currentNameSetName_;  
  
  protected Name currentChannelSetName_;  
  
  protected CircusProcess currentProcess_;
  protected CircusAction currentAction_;
  protected NameSet currentNameSet_;
  protected ChannelSet currentChannelSet_;

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
  protected boolean circusQualifiedParams_ = false;  
  protected boolean isCheckingStatePara_ = false;
    
  //the visitors used to typechecker a Circus program
  protected Checker<Signature> signatureChecker_;
  protected ActionChecker actionChecker_;
  protected Checker<CircusCommunicationList> commandChecker_;
  protected Checker<List<NameTypePair>> commChecker_;
  protected ProcessChecker processChecker_;
  protected Checker<Signature> processParaChecker_;
  protected BasicProcessChecker basicProcessChecker_;
  // auxiliar visitor to typechecker a channel declaration
  protected Checker<Boolean> channelDeclChecker_;
  // auxiliar visitor to find used channels into a process
  protected Checker<NameList> channelsUsedChecker_;
  protected boolean shouldCreateLetMu_;
  protected CircusConcreteSyntaxSymbolVisitor concreteSyntaxSymbolVisitor_;

  protected WarningManager warningManager_;
  
  // list of call names with their corresponding list of pending errors.
  // as one could have multiple names, we use a list of pairs rather than a map.
  protected List<Pair<Name, List<ErrorAnn>>> pendingCallErrors_;
  
  public TypeChecker(net.sourceforge.czt.typecheck.circus.impl.Factory factory,
                     SectionManager sectInfo)
  {
    this(factory, sectInfo, PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT,
        PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT);
  }

  public TypeChecker(net.sourceforge.czt.typecheck.circus.impl.Factory factory,
                     SectionManager sectInfo,
                     boolean recursiveTypes,
                     boolean sortDeclNames)
  {
    // create all the checkers as default - for Z
    super(factory, sectInfo, recursiveTypes, sortDeclNames);     
    
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
    basicProcessChecker_ = new BasicProcessChecker(this);
    
    actionChecker_ = new ActionChecker(this);
    commandChecker_ = new CommandChecker(this);
    commChecker_ = new CommunicationChecker(this);
    processChecker_ = new ProcessChecker(this);
    
    warningManager_ = new WarningManager(TypeChecker.class, sectInfo);
    warningManager_.setMarkup(markup_);
    concreteSyntaxSymbolVisitor_ = CircusUtils.CIRCUS_CONCRETE_SYNTAXSYMBOL_VISITOR;    
    pendingCallErrors_ = factory.list();
    
    currentProcessName_ = null;
    currentActionName_ = null;
    currentNameSetName_ = null;
    currentChannelSetName_ = null;
    currentProcess_ = null;
    currentAction_ = null;
    currentNameSet_ = null;
    currentChannelSet_ = null;
    stateName_ = null;
    onTheFlyProcesses_ = null;

    circusFormalParameters_ = false;
    circusQualifiedParams_ = false;
    isCheckingStatePara_ = false;

    shouldCreateLetVars_ = PROP_TYPECHECK_CREATE_LETVAR_DEFAULT;
    shouldCreateLetMu_ = PROP_TYPECHECK_RESOLVE_MUTUAL_REC_DEFAULT;    

    // raise warnings has priority over hide warnings (e.g., can only hide if not raising)
    warningManager_.setWarningOutput(PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT);
    
//    channels_ = new ArrayList<ChannelInfo>();
//    chansets_ = getFactory().createZNameList();    
//    muProcesses_ = getFactory().createZNameList();    
//    muActions_ = getFactory().createZNameList();    
//    actions4PostCheck_ = getFactory().createZNameList();    
//    
//    // auxiliar visitors
//    channelDeclChecker_ = new GenChannelDeclChecker(this);
//    channelsUsedChecker_ = new ChannelsUsedChecker(this);
    
    // override default type environment classes to be 
    // a Circus type environment, which allows extra info for checkers.
    typeEnv_ = new TypeEnv(getFactory());
    pending_ = new TypeEnv(getFactory());
  }  

  @Override
public net.sourceforge.czt.typecheck.circus.impl.Factory getFactory()
  {
    return (net.sourceforge.czt.typecheck.circus.impl.Factory) super.getFactory();
  }

  public WarningManager getWarningManager()
  {
    return warningManager_;
  }
  
  public boolean setCreateLetVar(boolean val)
  {
    boolean result = shouldCreateLetVars_;
    shouldCreateLetVars_ = val;
    return result;
  }

  @Override
  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    super.setPreamble(sectName, sectInfo);
  }    
}
