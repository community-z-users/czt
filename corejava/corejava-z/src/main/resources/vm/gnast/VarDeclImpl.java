
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
