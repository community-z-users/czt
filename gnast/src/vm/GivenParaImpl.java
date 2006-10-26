
  public ZNameList getNames()
  {
    NameList dnl = getNameList();
    if (dnl instanceof ZNameList) {
      return (ZNameList) dnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
