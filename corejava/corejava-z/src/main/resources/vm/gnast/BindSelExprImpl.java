
  public ZName getZName()
  {
    Name refName = getName();
    if (refName instanceof ZName) {
      return (ZName) refName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(refName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
