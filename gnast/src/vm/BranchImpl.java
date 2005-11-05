
  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  public ZDeclName getZDeclName()
  {
    DeclName declName = getDeclName();
    if (declName instanceof ZDeclName) {
      return (ZDeclName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    builder.append(String.valueOf(getDeclName()));
    if (getExpr() != null) {
        builder.append("<<");
        builder.append(getExpr().toString());
        builder.append(">>");
    }
    return builder.toString();
  }
