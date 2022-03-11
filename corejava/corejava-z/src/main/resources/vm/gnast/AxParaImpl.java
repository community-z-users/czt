
  /**
   * This is a convenience method.
   * It returns the ZSchText if SchText is an instance of
   * ZSchText and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.z.ast.ZSchText getZSchText()
  {
	  net.sourceforge.czt.z.ast.SchText schText = getSchText();
    if (schText instanceof net.sourceforge.czt.z.ast.ZSchText) {
      return (net.sourceforge.czt.z.ast.ZSchText) schText;
    }
    final String message = "Expected the default (Z) implementation of SchText" +
      " but found " + String.valueOf(schText);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.ZNameList getName()
  {
	  net.sourceforge.czt.z.ast.NameList dnl = getNameList();
    if (dnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) dnl;
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(dnl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
