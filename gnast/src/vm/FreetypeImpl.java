
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
    builder.append(" ::= ");
    if (getBranch() != null) {
      java.util.Iterator<Branch> it = getBranch().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append(" | ");
      }
    } else builder.append(" null ");
    return builder.toString();
  } 
