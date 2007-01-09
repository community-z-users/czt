
  public ZName getZName()
  {
    Name name = getName();
    if (name instanceof ZName) {
      return (ZName) name;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

