
  /**
   * This is a convenience method.
   * It returns the ZSchText if SchText is an instance of
   * ZSchText and throws an UnsupportedAstClassException otherwise.
   */
  public ZSchText getZSchText()
  {
    SchText schText = getSchText();
    if (schText instanceof ZSchText) {
      return (ZSchText) schText;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public ZDeclNameList getDeclName()
  {
    DeclNameList dnl = getDeclNameList();
    if (dnl instanceof ZDeclNameList) {
      return (ZDeclNameList) dnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
