
  public ZName getZName()
  {
    Name name = getOpName();
    if (name instanceof ZName) {
      return (ZName) name;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

