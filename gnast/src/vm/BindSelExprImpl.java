
  public ZName getZName()
  {
    Name refName = getName();
    if (refName instanceof ZName) {
      return (ZName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
