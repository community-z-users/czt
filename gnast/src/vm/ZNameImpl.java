
  public net.sourceforge.czt.z.util.OperatorName getOperatorName()
  {
    try {
      return new net.sourceforge.czt.z.util.OperatorName(this);
    }
    catch(net.sourceforge.czt.z.util.OperatorName.OperatorNameException e) {
      return null;
    }
  }
  
  public net.sourceforge.czt.z.util.OperatorName getOperatorName(
    net.sourceforge.czt.z.util.Fixity fixity)
  {
    try {
      return new net.sourceforge.czt.z.util.OperatorName(this.getWord(), this.getStrokeList(), fixity);
    }
    catch(net.sourceforge.czt.z.util.OperatorName.OperatorNameException e) {
      return null;
    }  
  }
  

  /**
   * This is a convenience method.
   * It returns the ZStrokeList if ZStrokeList is an instance of
   * ZStrokeList and throws an UnsupportedAstClassException otherwise.
   */
  public ZStrokeList getZStrokeList()
  {
    StrokeList strokeList = getStrokeList();
    if (strokeList instanceof ZStrokeList) {
      return (ZStrokeList) strokeList;
    }
    final String message = "Expected the default (Z) implementation of StrokeList" +
      " but found " + String.valueOf(strokeList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

