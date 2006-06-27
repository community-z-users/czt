
  /**
   * This is a convenience method.
   * It returns the ZDeclNameList if DeclNameList is an instance of
   * ZDeclNameList or throws an UnsupportedAstClassException otherwise.
   */
  public ZDeclNameList getZDeclNameList()
  {
    DeclNameList dnl = getDeclNameList();
    if (dnl instanceof ZDeclNameList) {
      return (ZDeclNameList) dnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }