
  /**
   * This is a convenience method.
   * It returns the ZExprList if ExprList is an instance of
   * ZExprList or throws an UnsupportedAstClassException otherwise.
   */
  public ZExprList getZActuals()
  {
    ExprList el = getActuals();
    if (el instanceof ZExprList) {
      return (ZExprList) el;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }