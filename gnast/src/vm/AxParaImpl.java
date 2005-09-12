
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
    String message =
      "ZSchText expected but found " + schText.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
