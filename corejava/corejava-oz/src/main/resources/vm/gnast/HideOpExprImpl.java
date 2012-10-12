
  public ZNameList getName()
  {
    NameList refNameList = getNameList();
    if (refNameList instanceof ZNameList) {
      return ((ZNameList) refNameList).getName();
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(refNameList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

