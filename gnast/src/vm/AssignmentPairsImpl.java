
  public ZNameList getZLHS()
  {
    NameList rnl = getLHS();
    if (rnl instanceof ZNameList) {
      return (ZNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public ZExprList getZRHS()
  {
    ExprList expr = getRHS();
    if (expr instanceof ZExprList) {
      return (ZExprList) expr;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

