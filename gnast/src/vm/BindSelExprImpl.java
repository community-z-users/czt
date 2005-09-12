
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
    String message =
      "ZRefName expected but found " + refName.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
