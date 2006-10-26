
  public ZNameList getName()
  {
    NameList refNameList = getNameList();
    if (refNameList instanceof ZNameList) {
      return ((ZNameList) refNameList).getName();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

