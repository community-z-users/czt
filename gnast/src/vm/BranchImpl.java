
  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName (NewName) is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  public ZDeclName getZDeclName()
  {
    DeclName declName = getDeclName();
    if (declName instanceof ZDeclName) {
      return (ZDeclName) declName;
    }
    String message =
      "ZDeclName expected but found " + declName.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
