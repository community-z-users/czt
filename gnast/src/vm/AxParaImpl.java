
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

  public ZNameList getName()
  {
    NameList dnl = getNameList();
    if (dnl instanceof ZNameList) {
      return (ZNameList) dnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
