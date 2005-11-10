
  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName (ChanName) is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefName getZChanName()
  {
    RefName refName = getChanName();
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  /**
   * This is a convenience method.
   * It returns the ZExprList if ExprList (GenActuals) is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  public ZExprList getZGenActuals()
  {
    ExprList expr = getGenActuals();
    if (expr instanceof ZExprList) {
      return (ZExprList) expr;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }