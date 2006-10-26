
  public ZExprList getZActuals()
  {
    ExprList el = getActuals();
    if (el instanceof ZExprList) {
      return (ZExprList) el;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
