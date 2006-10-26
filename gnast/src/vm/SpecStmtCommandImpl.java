
  public ZNameList getZFrame()
  {
    NameList rnl = getFrame();
    if (rnl instanceof ZNameList) {
      return (ZNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
