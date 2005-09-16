  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  public ZDeclName getZDeclName()
  {
    DeclName declName = getOpName();
    if (declName instanceof ZDeclName) {
      return (ZDeclName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

