  /**
   * This is a convenience method.
   * It returns the ZName if Name is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  public ZName getZName()
  {
    Name refName = getName();
    if (refName instanceof ZName) {
      return (ZName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

