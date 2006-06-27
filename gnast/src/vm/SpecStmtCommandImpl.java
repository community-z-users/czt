
  /**
   * This is a convenience method.
   * It returns the ZRefNameList if RefNameList is an instance of
   * ZRefNameList or throws an UnsupportedAstClassException otherwise.
   */
  public ZRefNameList getZFrame()
  {
    RefNameList rnl = getFrame();
    if (rnl instanceof ZRefNameList) {
      return (ZRefNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }