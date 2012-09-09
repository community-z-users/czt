
  public ZNameList getName()
  {
    NameList dnl = getNameList();
    if (dnl instanceof ZNameList) {
      return (ZNameList) dnl;
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(dnl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
