  /**
   * This is a convenience method.
   * It returns the ZNameList if NameList is an instance of
   * ZNameList or throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZNameList getZGenFormals();

  /**
   * This is a convenience method.
   * It returns the ZName if Name is an instance of
	   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZName getZName();

  /**
   * Basic process can have parameters or indexes. That is, it returns
   * if CircusUtils.isBasicProcess(getCircusProcess(), since basic processes
   * can have parameters or indexes (in one-level only, though).
   * @return if the inner process is basic or compound otherwise
   */
  boolean isBasicProcess();
  
  /**
   * This is a convenience method for CircusUtils.getBasicProcess(getCircusProcess()).
   * It throws a UnsupportedAstClassException exception if not isBasicProcess().
   * @return
   */
  net.sourceforge.czt.circus.ast.BasicProcess getCircusBasicProcess();      

  /**
   * Updates the declaring basic process in this process paragraph, if it is a 
   * basic process (according to isBasicProcess()), or raises a UnsupportedAstClassException
   * exception otherwise. That is, if isBasicProcess(), it either updates the
   * appropriate inner process for this paragraph depending whether it is a 
   * parameterised/indexed basic process or a simple one.
   * 
   * @param term the term to set the inner process with.
   */
  void setCircusBasicProcess(net.sourceforge.czt.circus.ast.BasicProcess term);  

