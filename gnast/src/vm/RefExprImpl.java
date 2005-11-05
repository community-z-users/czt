
  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefName getZRefName()
  {
    RefName refName = getRefName();
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    if (!getMixfix()) {
      // Reference + Generic instantiation
      builder.append(String.valueOf(getRefName()));
      if (getExprList() instanceof ZExprList)  {
          builder.append(getZExprList().isEmpty() ? "" : getZExprList().toString());
      } else
          builder.append(String.valueOf(getExprList()));
    } else {
      // Generic op. application: ex: S \rel T
      builder.append("(");
      builder.append(String.valueOf(getRefName()));
      builder.append(")");
      if (getExprList() instanceof ZExprList) {
        builder.append("~(");
        java.util.Iterator<Expr> it = getZExprList().iterator();
        while(it.hasNext()) {
            builder.append(it.next().toString());
            if (it.hasNext())
                builder.append(", ");
        }
        builder.append(")");
      } else
        builder.append(String.valueOf(getExprList()));
    }
    return builder.toString();
  }
 
