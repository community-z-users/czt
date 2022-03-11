  /**
   * Basic process can have parameters or indexes. That is, it returns
   * if (getCircusProcess() instanceof BasicProcess). As nested parameterised
   * processes are not allowed, this is enough to charachterise 
   * parameterised/indexed basic processes.
   * @return if the inner process is basic or compound otherwise
   */
  boolean isBasicProcess();

  /**
   * This is a convenience method for getCircusProcess() cast as BasicProcess.
   * It throws a UnsupportedAstClassException exception if not isBasicProcess().
   * @return
   */
  net.sourceforge.czt.circus.ast.BasicProcess getCircusBasicProcess();  
