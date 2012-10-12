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
    final String message = "Expected the default (Z) implementation of SchText" +
      " but found " + String.valueOf(schText);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

