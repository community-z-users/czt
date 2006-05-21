
  public ZDeclNameList getDeclName()
  {
    DeclNameList dnl = getDeclNameList();
    if (dnl instanceof ZDeclNameList) {
      return (ZDeclNameList) dnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
