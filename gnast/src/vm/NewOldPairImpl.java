
  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName (NewName) is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  public ZDeclName getZDeclName()
  {
    DeclName declName = getNewName();
    if (declName instanceof ZDeclName) {
      return (ZDeclName) declName;
    }
    String message =
      "ZDeclName expected but found " + declName.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName (OldName) is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefName getZRefName()
  {
    RefName refName = getOldName();
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    String message =
      "ZRefName expected but found " + refName.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
