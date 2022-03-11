
  /**
   * This is a convenience method.
   * It returns the ZName if Name is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZName getZName();

  /**
   * Returns whether the inner action is parameterised or not.
   * This can be useful to check whether calls to the recursive 
   * variable require parameters or not.
   * @return
   */
  boolean isParameterised(); 