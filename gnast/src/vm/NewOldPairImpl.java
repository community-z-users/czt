
  public ZName getZDeclName()
  {
    Name declName = getNewName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public ZName getZRefName()
  {
    Name refName = getOldName();
    if (refName instanceof ZName) {
      return (ZName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

