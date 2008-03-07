/*
  Copyright (C) 2007 Leo Freitas
  Copyright (C) 2007 Petra Malik
  This file is part of the CZT project.

  The CZT project contains free software;
  you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.circus;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.Model;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.util.Factory;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.Source;
//import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.ZUtils;

public class ParserState
  extends net.sourceforge.czt.parser.z.ParserState
{        
  /**
   * Unique number seed for implicitly declared action names.
   */                         
  private static int implicitlyActUniqueNameSeed_ = 0;
    
  /**
   * Unique number seed for implicitly declared process names.
   */  
  private static int implicitlyProcUniqueNameSeed_ = 0;

  /**
   * Keeps track of current basic process scope on multiple environments.
   * This flag is set to true right upon entering the scope, but still 
   * before assigning to basicProcess_.
   */  
  private boolean isWithinMultipleEnvBasicProcessScope_ = false;
  
  /**
   * Keeps track of the last process name within a paragrph. It is 
   * important to tackle multiple environment basic processes.
   */
  //private Name processName_ = null;
  
  /**
   * Process paragraph's generic parameters. That is important for BasicProcesses
   */
  //private NameList processGen_ = null;
  
  private ProcessPara processPara_ = null;
  
  private BasicProcess basicProcess_ = null;
  
  private Model fModel = null;
  
  /**
   * LocInfo for the BasicProcess entering scope position. Useful to build/use
   * the ProcessPara formed by processName_, processGen_, and basicProcess_.
   */
  private LocInfo  processLoc_ = null;
  
  private Para statePara_ = null;
  
  /**
   * <p>List of implicitly declared actions as action paragraphs,
   * where the action name is given according to
   * <code>implicitlyActUniqueNameSeed_</code> static field.</p>
   *
   * <p>This list is cleared at the <code>BasicProcess</code> related
   * productions so that they are always related to the current basic
   * process being parsed.</p>
   *
   * <p>This is in fact the getOnTheFlyPara() of current process</p>
   * REFACTORED: use position and put then in the order they appear
   */
   //private List<ActionPara> implicitlyDeclActPara_ =
   //   new ArrayList<ActionPara>();
   
   private List<Para> locallyDeclPara_ =
      new ArrayList<Para>();   
  
  /**
   * <p>List of implicitly declared processes as process paragraphs,
   * where the process name is given according to
   * &lt;code&gt;implicitlyProcUniqueNameSeed_&lt;/code&gt; static
   * field.</p>
   *
   * <p>This list is cleared at the <code>ZSect</code> related
   * productions so that they are always related to the current Z
   * section being parsed.</p>
   */
  private List<ProcessPara> implicitlyDeclProcPara_ =
    new ArrayList<ProcessPara>();
  
  private CircusAction mainAction_ = null;

  private Factory factory_ = new Factory();
  
  public ParserState(Source loc) {
      super(loc);
      clearAllProcessInformation();
      //processGen_ = factory_.createZNameList();
  }   
  
  /**
   * Clears the implicitly declared actions cache for the current
   * <code>BasicProcess/code>.  It also resets the unique name seed to
   * zero.
   */  
  protected void clearBasicProcessParaCache()
  { 
    implicitlyActUniqueNameSeed_ = 0;        
    locallyDeclPara_.clear();
  }
  
  /**
   * Clears the implicitly declared processes cache for the current
   * <code>ZSect</code>.  It also resets the unique name seed to zero.
   */
  protected void clearSectProcessOnTheFlyCache()
  {
    implicitlyProcUniqueNameSeed_ = 0;
    implicitlyDeclProcPara_.clear();      
  }
  
  /**
   * Clears the implicitly declared actions and their name seed;
   * the current main action, the current basic process, and the
   * list of locally declared paragraphs.
   */
  public void clearBasicProcessInformation() {      
      // only structural items: no loc or process name, or bp instance
      setMainAction(null);      
      setStatePara(null);      
      clearBasicProcessParaCache();
      //clearBasicProcessOnTheFlyCache();
      //clearBasicProcessLocalParaCache();      
      ////clearBasicProcessScopeWarnings();
  }
  
  public void clearAllProcessInformation() {      
      clearSectProcessOnTheFlyCache();
      clearBasicProcessInformation();      
      
      basicProcess_ = null;      
      processLoc_ = null;
      processPara_ = null;
      //processName_ = null;      
      //setProcessGenFormals(null); // sets it to the empty list.      
      
      clearSectBasicProcessScopeWarnings();
      clearSectBasicProcessEndWarning();      
      clearRefinementModel();
  }
  

  /**
   * Creates a unique string for implicitly declared actions.
   */
  public String createImplicitlyDeclActUniqueName()
  {
    //DO NOT ADD THIS ASSERT HERE, SINCE THEY MAY BE ADDED OUTSIDE AN OPEN SCOPE
    //assert hasBasicProcess() : "There is no current basic process for implicitly declared action";
    String result = CircusUtils.DEFAULT_IMPLICIT_ACTION_NAME_PREFIX + implicitlyActUniqueNameSeed_;
    implicitlyActUniqueNameSeed_++;
    return result;
  }

  /**
   * Creates a unique string for implicitly declared processes.
   */
  public String createImplicitlyDeclProcUniqueName()
  { 
    String result = CircusUtils.DEFAULT_IMPLICIT_PROCESS_NAME_PREFIX + implicitlyProcUniqueNameSeed_;
    implicitlyProcUniqueNameSeed_++;
    return result;
  }

  /**
   * Add an implicitly declared action to the current
   * <code>BasicProcess</code> cache.  It also includes an
   * <code>OnTheFlyDefAnn</code> for the action the paragraph defines.
   */
  public void addImplicitlyDeclActionPara(ActionPara ap)
  {    
    //DO NOT ADD THIS ASSERT HERE, SINCE THEY MAY BE ADDED OUTSIDE AN OPEN SCOPE.
    //assert hasBasicProcess() : "There is no current basic process for implicitly declared action";
    assert !isImplicitlyDeclaredActionPara(ap) :
      "Action already had an on-the-fly annotation";
    ap.getCircusAction().getAnns().add(factory_.createOnTheFlyDefAnn());
    locallyDeclPara_.add(ap);
    //implicitlyDeclActPara_.add(ap);    
  }
  
  public boolean isImplicitlyDeclaredActionPara(ActionPara ap) {
      return ap.getCircusAction().getAnn(OnTheFlyDefAnn.class) != null;
  }

  public void addLocallyDeclPara(Para p)
  {     
    // avoid repeated at parsing? or let the typechecker take care of it
    // assert !locallyDeclPara_.contains(p);
    locallyDeclPara_.add(p);
  }
  
  /**
   * Add an implicitly declared process to the current
   * <code>ZSect</code> cache.  It also includes an
   * <code>OnTheFlyDefAnn</code> for the process the paragraph
   * defines.
   */
  public void addImplicitlyDeclProcessPara(ProcessPara pp)
  {
    assert pp.getCircusProcess().getAnn(OnTheFlyDefAnn.class) == null :
      "Process already had an on-the-fly annotation";
    pp.getCircusProcess().getAnns().add(factory_.createOnTheFlyDefAnn());
    implicitlyDeclProcPara_.add(pp);
  }
  
  // To be called by the parser at the update ZSect production 
  public List<ProcessPara> getImplicitlyDeclProcPara()
  {    
    return implicitlyDeclProcPara_;
  }
  
  // Should not be called outside the ParserState. 
  // It is called through updateBasicProcess. 
  // Leave protected in case derived classes need it.
  //protected List<ActionPara> getImplicitlyDeclActPara()
  //{    
  //  return implicitlyDeclActPara_;
  //}  
  
  // Should not be called outside the ParserState. 
  // It is called through updateBasicProcess
  // Leave protected in case derived classes need it.
  protected List<Para> getLocallyDeclPara()
  {    
    return locallyDeclPara_;
  }
  
  protected boolean isValidStatePara(Para p)
  {
     return ZUtils.isHorizontalDef(p) || CircusUtils.isSchema(p);
  }

  /**
   * Adds a &lt;code&gt;CircusStateAnn&lt;/code&gt; annotation to the given paragraph.
   * The code also checks the paragraph is indeed a valid schema, and an error is
   * report if a problem is found.
   */
  public void addCircusStateAnn(Para para) {     
     assert isValidStatePara(para) : "Invalid paragraph for process state";
     para.getAnns().add(factory_.createCircusStateAnn());
  }
  
  // [~ | true ~]
  protected Expr createEmptySchExpr() {
      Expr result = factory_.createSchExpr(
          factory_.createZSchText(
            factory_.createZDeclList(), factory_.createTruePred()));
      return result;
  }
  
  protected Name createDefaultProcessStateName(LocInfo l) {
      Name dn = factory_.createZName(CircusUtils.DEFAULT_PROCESS_STATE_NAME);
      addLocAnn(dn, l);
      return dn;
  }  

  public Para createDefaultStatePara(LocInfo l) {            
      Name n = createDefaultProcessStateName(l);
      
      // Creates a horizontal schema: name == e as ConstDecl
      ConstDecl cd = factory_.createConstDecl(n, createEmptySchExpr());
      addLocAnn(cd, l);      
      ZDeclList decls = factory_.createZDeclList(factory_.list(cd));           
      ZSchText st = factory_.createZSchText(decls, null);
      addLocAnn(st, l);

      // no generic arguments for state schema
      ZNameList zdnl = factory_.createZNameList();
      Para result = factory_.createAxPara(zdnl, st, Box.OmitBox);

      // add CircusStateAnn to paragraph
      addCircusStateAnn(result);
      addLocAnn(result, l);
      
      return result;
  }
  
  /**
   * Enters a basic process scope, provided there isn't one already,
   * since nested scope processes are not allowed. If the result is
   * false, the parser ought to flag an error. The location information
   * object defines where the process was first declared. This is
   * particularly useful for multiply environment process declarations.
   */
  public boolean enterBasicProcessScope(LocInfo loc) {          
    // If there is a process name, then we can enter a valid scope.
    boolean result = !isWithinMultipleEnvBasicProcessScope();
    if (result) {        
        processLoc_ = loc;
        isWithinMultipleEnvBasicProcessScope_ = true;
    }
    return result;
  }
  
  /**
   * Clears the current basic process scope, provided one exists.
   * If it doesn't nothing change, and the parser should raise a warning.
   */
  public boolean exitBasicProcessScope() {      
      // get ; clear the scope information.
      // if originally false, exit will return false and
      // the parser shall flag an warning about umatched scopes.
      boolean result = isWithinMultipleEnvBasicProcessScope();
      basicProcess_ = null;      
      processLoc_ = null;
      processPara_ = null;
      //processName_ = null;      
      //setProcessGenFormals(null); // sets it to the empty list.
      isWithinMultipleEnvBasicProcessScope_ = false;      
      return result;      
  }  
  
  public boolean isWithinMultipleEnvBasicProcessScope() {
      /**
       * NOTE: This variable name is misleading a little bit.
       *       Even within singled environment scope, it is set.
       *       Nevertheless, the code for handling both single env 
       *       is left within the production, whereas the code for 
       *       multiple env is scattered across multiple productions.
       */
      return isWithinMultipleEnvBasicProcessScope_;
  }
  
  public void setMainAction(CircusAction action) {
      mainAction_ = action;
  }
  
  public CircusAction getMainAction() {
      return mainAction_;
  }
  
  public void setStatePara(Para para) {
      statePara_ = para;
  }
  
  public Para getStatePara() {
      return statePara_;
  }
  
  public ProcessPara getProcessPara() {
      return processPara_;
  }
  
  public void setProcessPara(ProcessPara pp) {
      processPara_ = pp;
  }  
 
  public Name getProcessName() {      
      return processPara_ != null ? processPara_.getName() : null;
  }
  
  public NameList getProcessGenFormals() {      
      return processPara_ != null ? processPara_.getGenFormals() : null;
  }
  
  public boolean hasProcessPara() {
      return processPara_ != null;
  }  
  
  public boolean hasProcessName() {
      return hasProcessPara() & processPara_.getName() != null;
  }  
  
  /*
  public void setProcessGenFormals(NameList nl) {
      processGen_ = (nl == null ? factory_.createZNameList() : nl);
  }
  
  public void setProcessName(Name name) {
      processName_ = name;
  }  
 */
  
  public void setBasicProcess(BasicProcess bp) {
      assert bp != null : "Invalid basic process (null).";
      assert isWithinMultipleEnvBasicProcessScope() : "Cannot set process outside an open scope";
      basicProcess_ = bp;
  }
  
  public BasicProcess getBasicProcess() {
      return basicProcess_;
  }
  
  public boolean hasMainAction() {
      return mainAction_ != null;
  }
   
  public boolean hasState() {
      return statePara_ != null;
  }
  
  public boolean hasBasicProcess() {
      return basicProcess_ != null;
  }
  
  public boolean updateBasicProcessInformation() {
      boolean result = isWithinMultipleEnvBasicProcessScope() && hasBasicProcess() && hasMainAction();      
      if (result) {
          assert processLoc_ != null : "Invalid original location";
          
          // get state or create a default one
          Para statePara = getStatePara();
          if (statePara == null) {
              statePara = createDefaultStatePara(processLoc_);
              assert statePara != null : "Invalid default state creation";
              addLocallyDeclPara(statePara);
          }
          // else, it is already in either list
          assert (getLocallyDeclPara().contains(statePara));
//                  &&
//                  !getImplicitlyDeclActPara().contains(statePara)) 
//                 ||
//                 (getImplicitlyDeclActPara().contains(statePara) &&
//                  !getLocallyDeclPara().contains(statePara));                 
          
          /*
          // copy the paragraphs into a ZParaList
          ZParaList localPara = factory_.createZParaList(getLocallyDeclPara());
          ZParaList onTheFlyPara = factory_.createZParaList(getImplicitlyDeclActPara());
          
          // get main action
          CircusAction mainAction = getMainAction();      

          // create new basic process to be used.          
          basicProcess_.setStatePara(statePara);
          basicProcess_.setLocalPara(localPara);
          basicProcess_.setOnTheFlyPara(onTheFlyPara);
          basicProcess_.setMainAction(mainAction);      
           */
          
          basicProcess_.getZParaList().addAll(getLocallyDeclPara());
          //basicProcess_.getZParaList().addAll(getImplicitlyDeclActPara());
          
          assert checkBasicProcessStructuralInvariant(statePara) 
            : "basic process failed structural invariant in ParserState";
          
          addLocAnn(basicProcess_, processLoc_);
      }
      return result;
  }
  
  private boolean checkBasicProcessStructuralInvariant(Para statePara)
  {
    boolean result = statePara.equals(basicProcess_.getStatePara());    
    if (result)
    {    
      result = getMainAction().equals(basicProcess_.getMainAction());
      if (result)
      {        
        // check if the basic process protocol is ok        
        result = getLocallyDeclPara().equals(basicProcess_.getZParaList());
        if (result)
        {
          result = getLocallyDeclPara().containsAll(basicProcess_.getLocalPara());
          if (result)
          {
            result = getLocallyDeclPara().containsAll(basicProcess_.getOnTheFlyPara());
          }
        }
      }
    }
    return result;
  }
  
  public BasicProcess cloneBasicProcessWithAnns() {
      assert isWithinMultipleEnvBasicProcessScope() && hasBasicProcess() : 
          "Cannot clone basic process outside scope or with null bp";
      BasicProcess result = (BasicProcess)basicProcess_.create(basicProcess_.getChildren());
      // copy the annotations as well. This will include the location annotation.
      result.getAnns().addAll(basicProcess_.getAnns());
      return result;
  }
  
  /**
   * Check whether the given para list is contained within the parsing state
   * either as locally declared para or implicitly declared action para.
   */
  public boolean isKnownPara(List<Para> ipl) {
      for(Para para : ipl) {
          if (//!implicitlyDeclActPara_.contains(para) &&
              !locallyDeclPara_.contains(para))
              return false;
      }
      return true;
  }
  
  private List<Pair<String, LocInfo>> processScopeWarnings_ = 
      new ArrayList<Pair<String, LocInfo>>();
  
  // procName, LocInfo
  private Pair<Name, LocInfo> processEndWarning_;
  
  public List<Pair<String, LocInfo>> getProcessScopeWarnings() {
      return processScopeWarnings_;      
  }
  
  public Pair<Name, LocInfo> getProcessEndWarning() {
      return processEndWarning_;
  }
  
  public void addProcessScopeWarning(String msg, LocInfo loc) {
      processScopeWarnings_.add(new Pair<String, LocInfo>(msg, loc));
  }  
  
  public void addProcessEndWarning(Name procName, LocInfo loc) {  
      assert processEndWarning_ == null : "Cannot have duplicated CIRCEND warnings";
      final String msg = java.text.MessageFormat.format(
            CircusParseMessage.MSG_MISSING_BASIC_PROCESS_CIRCEND.getMessage(), 
               new Object[] { procName, loc });  
      processEndWarning_ = new Pair<Name, LocInfo>(procName, loc);
  }  
              
  public void clearSectBasicProcessEndWarning() {      
      processEndWarning_ = null;
  }
    
  public void clearSectBasicProcessScopeWarnings() {
     processScopeWarnings_.clear();
  }
  
  public Model getRefinementModel() {
      return fModel;
  }
   
  public void setRefinementModel(Model model) {
      fModel = model;
  }
  
  public void clearRefinementModel() {
      fModel = null;
  }
}