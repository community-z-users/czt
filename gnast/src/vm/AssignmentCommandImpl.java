
  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName (LHS) is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefNameList getZLHS()
  {
    RefNameList rnl = getLHS();
    if (rnl instanceof ZRefNameList) {
      return (ZRefNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  /**
   * This is a convenience method.
   * It returns the ZExprList if ExprList (RHS) is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  public ZExprList getZRHS()
  {
    ExprList expr = getRHS();
    if (expr instanceof ZExprList) {
      return (ZExprList) expr;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public String toString()
  {
    StringBuilder builder = new StringBuilder("(");
    if (getLHS() instanceof ZRefNameList) {
      java.util.Iterator<RefName> it = getZLHS().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append(", ");
      }
    } else {
      builder.append(String.valueOf(getLHS()));
    }
    builder.append(" := ");
    if (getRHS() instanceof ZExprList) {
      java.util.Iterator<Expr> it = getZRHS().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append(", ");
      }
    } else {
      builder.append(String.valueOf(getRHS()));
    } 
    builder.append(")");
    return builder.toString();
  }


