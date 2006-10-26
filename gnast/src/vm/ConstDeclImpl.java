
  public ZName getZName()
  {
    Name declName = getName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
