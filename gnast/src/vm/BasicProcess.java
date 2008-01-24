  /**
   * This is a convenience method. It returns the state paragraph within the getZParaList().
   * If one has not been declared, a default (empty) state paragraph (i.e., horizontal box 
   * named CircusUtils.DEFAULT_PROCESS_STATE_NAME with empty declarations and true predicate) 
   * is returned. The method checks that only one such paragraph exists, that it has a 
   * CircusStateAnn in it, and that if it is an ActionPara it must have a OnTheFlyAnn as well.
   * All these invariants are guaranteed by both the parser and typechecker. 
   */
  net.sourceforge.czt.z.ast.Para getStatePara();
  
  /**
   * This is a convenience method. It returns the main action within the getZParaList().
   * The method checks that only one such paragraph exists, that it has a 
   * OnTheFlyAnn in it, and that its name is CircusUtils.DEFAULT_MAIN_ACTION_NAME.
   * All these invariants are guaranteed by both the parser and typechecker. 
   */  
  net.sourceforge.czt.circus.ast.CircusAction getMainAction(); 
  
  /**
   * This is a convenience method. It returns a unmodifiable list of declared paragraphs 
   * within the getZParaList(); they may be either Circus or Z paragraphs. 
   * That is, all paragraphs from getZParaList() that have not been declared on-the-fly.
   * All these invariants are guaranteed by both the parser and typechecker. 
   */   
  java.util.List<? extends net.sourceforge.czt.z.ast.Para> getLocalPara();    
    
  /**
   * This is a convenience method. It returns a unmodifiable list of on-the-fly paragraphs 
   * within the getZParaList(); they can only be ActionPara, since there are no Z on-the-fly paragraphs.
   * That is, all paragraphs from getZParaList() that have been declared on-the-fly.
   * All elements in the resulting list contain a OnTheFlyAnn.
   * All these invariants are guaranteed by both the parser and typechecker. 
   */   
  java.util.List<net.sourceforge.czt.circus.ast.ActionPara> getOnTheFlyPara();    

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of paragraphs for the basic process. It contains both Z and Circus paragraphs.
   * It may throw a UnsupportedAstClassException is #getParaList() is a ParaJoker.
   * This method forms a partition between getOnTheFlyPara() and getLocalPara().
   * All these invariants are guaranteed by both the parser and typechecker.    
   */
  net.sourceforge.czt.z.ast.ZParaList getZParaList();

  /**
   * This is a convenience method. It represents the non-null name of the 
   * (possibly implicitly) declared process state name. 
   */
  net.sourceforge.czt.z.ast.Name getStateParaName();

  /**
   * This is a convenience method. It casts getStateParaName() into a ZName.
   */
  net.sourceforge.czt.z.ast.ZName getStateParaZName();  
