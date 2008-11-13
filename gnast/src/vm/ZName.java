
  /**
   * Returns an OperatorName, if this name is an operator name,
   * <code>null</code> otherwise.
   */
  net.sourceforge.czt.z.util.OperatorName getOperatorName();

  /**
   * Returns an OperatorName with specific fixity, 
   * if this name is an operator name, <code>null</code> otherwise.
   */
  net.sourceforge.czt.z.util.OperatorName getOperatorName(
    net.sourceforge.czt.z.util.OperatorName.Fixity fixity);
  
  /**
   * This is a convenience method.
   * It returns the ZStrokeList if ZStrokeList is an instance of
   * ZStrokeList and throws an UnsupportedAstClassException otherwise.
   */
  ZStrokeList getZStrokeList();
