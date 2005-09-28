  /**
   * This is a convenience method.
   * It returns the list of RefName if the RefNameList is an instance of
   * ZRefNameList and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefNameList getName()
  {
    RefNameList refNameList = getRefNameList();
    if (refNameList instanceof ZRefNameList) {
      return ((ZRefNameList) refNameList).getRefName();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

