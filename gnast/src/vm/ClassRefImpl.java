  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefName getZRefName()
  {
    RefName refName = getRefName();
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

