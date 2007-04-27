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
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusStateAnn;
import net.sourceforge.czt.circus.ast.OnTheFlyDefAnn;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.util.Factory;
import net.sourceforge.czt.circus.util.PrintVisitor;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
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
   * Default name of state for stateless processes.
   */
  private static final String DEFAULT_PROCESS_STATE_NAME = "$$defaultSt"; 
    
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
   */  
  private BasicProcess basicProcess_ = null;
  
  private Para statePara_ = null;
  
  public ParserState(Source loc) {
      super(loc);
  }
  
  /**
   * <p>List of implicitly declared actions as action paragraphs,
   * where the action name is given according to
   * <code>implicitlyActUniqueNameSeed_</code> static field.</p>
   *
   * <p>This list is cleared at the <code>BasicProcess</code> related
   * productions so that they are always related to the current basic
   * process being parsed.</p>
   *
   * <p>REFACTORED: This is in fact the getOnTheFlyPara() of current process</p>*/
   private List<ActionPara> implicitlyDeclActPara_ =
      new ArrayList<ActionPara>();
      
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
  
  private PrintVisitor printVisitor_ = new PrintVisitor(); 
           
  /**
   * Clears the implicitly declared actions cache for the current
   * <code>BasicProcess/code>.  It also resets the unique name seed to
   * zero.
   */
  public void clearBasicProcessOnTheFlyCache()
  {           
    implicitlyActUniqueNameSeed_ = 0;    
    implicitlyDeclActPara_.clear();
  }
  
  public void clearBasicProcessLocalParaCache()
  {               
    locallyDeclPara_.clear();
  }
    
  /**
   * Clears the implicitly declared processes cache for the current
   * <code>ZSect</code>.  It also resets the unique name seed to zero.
   */
  public void clearSectProcessOnTheFlyCache()
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
      setMainAction(null);      
      setStatePara(null);
      clearBasicProcessOnTheFlyCache();
      clearBasicProcessLocalParaCache();
  }

  /**
   * Creates a unique string for implicitly declared actions.
   */
  public String createImplicitlyDeclActUniqueName()
  {
    //DO NOT ADD THIS ASSERT HERE, SINCE THEY MAY BE ADDED OUTSIDE AN OPEN SCOPE
    //assert isWithinMultipleEnvBasicProcessScope() : "There is no current basic process for implicitly declared action";
    String result = "$$implicitAct" + implicitlyActUniqueNameSeed_;
    implicitlyActUniqueNameSeed_++;
    return result;
  }

  /**
   * Creates a unique string for implicitly declared processes.
   */
  public String createImplicitlyDeclProcUniqueName()
  { 
    String result = "$$implicitProc" + implicitlyProcUniqueNameSeed_;
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
    //assert isWithinMultipleEnvBasicProcessScope() : "There is no current basic process for implicitly declared action";
    assert ap.getCircusAction().getAnn(OnTheFlyDefAnn.class) == null :
      "Action already had an on-the-fly annotation";
    ap.getCircusAction().getAnns().add(factory_.createOnTheFlyDefAnn());
    implicitlyDeclActPara_.add(ap);    
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
  
  public List<ActionPara> getImplicitlyDeclActPara()
  {    
    return implicitlyDeclActPara_;
  }
  
  public List<Para> getLocallyDeclPara()
  {    
    return locallyDeclPara_;
  }
  
  /**
   * Enters a basic process scope, provided there isn't one already,
   * since nested scope processes are not allowed. If the result is
   * false, the parser ought to flag an error.
   */
  public boolean enterBasicProcessScope(BasicProcess bp) {
    assert bp != null : "Invalid basic process scope (null)";
    boolean result = !isWithinMultipleEnvBasicProcessScope();
    if (result) {
        basicProcess_ = bp;    
    }
    return result;
  }
  
  /**
   * Clears the current basic process scope, provided one exists.
   * If it doesn't nothing change, and the parser should raise a warning.
   */
  public BasicProcess exitBasicProcessScope() {      
      /*
      BasicProcess result = null;
      if (isWithinMultipleEnvBasicProcessScope()) {
          result = basicProcess_;
          basicProcess_ = null;
      } 
      return result;
      */
      // or simply...
      BasicProcess result = basicProcess_;
      basicProcess_ = null;
      return result;
  }
  
  public Name createDefaultProcessStateName(LocInfo l) {
      Name dn = factory_.createZName(DEFAULT_PROCESS_STATE_NAME);
      addLocAnn(dn, l);
      return dn;
  }
  
  /**
 * Adds a &lt;code&gt;CircusStateAnn&lt;/code&gt; annotation to the given paragraph.
 * The code also checks the paragraph is indeed a valid schema, and an error is
 * report if a problem is found.
 */
public void addCircusStateAnn(Para para) {
    //checkCircusStateAnnParaIsSchema(para);
    para.getAnns().add(factory_.createCircusStateAnn());
}
  
// [~ | true ~]
  public Expr createEmptySchExpr() {
      Expr result = factory_.createSchExpr(
          factory_.createZSchText(
            factory_.createZDeclList(), factory_.createTruePred()));
      return result;
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
  
  public boolean isWithinMultipleEnvBasicProcessScope() {
      return basicProcess_ != null;
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
  
  public boolean hasMainAction() {
      return mainAction_ != null;
  }
   
  public boolean hasState() {
      return statePara_ != null;
  }
  
  BasicProcess getBasicProcess() {
      assert isWithinMultipleEnvBasicProcessScope() : "Invalid basic process scope (null)";
      return basicProcess_;
  }
  
  public String printBasicProcess() {      
      assert isWithinMultipleEnvBasicProcessScope() : "Invalid basic process scope (null)";
      return printBasicProcess(basicProcess_);
  }
  
  public String printBasicProcess(BasicProcess bp) {      
      assert bp != null : "Invalid basic process scope (null)";
      return printVisitor_.printBasicProcesses(bp);
  }
  
  public BasicProcess updateBasicProcessInformation(LocInfo l) {
      assert isWithinMultipleEnvBasicProcessScope() : "Invalid basic process scope (null)";
      assert hasMainAction() : "No main action available for current basic process";

      Para statePara = hasState() ? getStatePara() : createDefaultStatePara(l);      
      ZParaList localPara = factory_.createZParaList(getLocallyDeclPara());
      ZParaList onTheFlyPara = factory_.createZParaList(getImplicitlyDeclActPara());      
      basicProcess_.setStatePara(statePara);
      basicProcess_.setLocalPara(localPara);
      basicProcess_.setOnTheFlyPara(onTheFlyPara);
      basicProcess_.setMainAction(getMainAction());
      return basicProcess_;
  }
}
