
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


