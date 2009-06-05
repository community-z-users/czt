
  public ZName getZName()
  {
    Name name = getName();
    if (name instanceof ZName) {
      return (ZName) name;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(name);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

