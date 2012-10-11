
  public ZName getZName()
  {
    Name declName = getName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
