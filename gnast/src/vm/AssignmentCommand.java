  /**
   * This is a convenience method.
   * It returns the ZRefNameList if RefNameList (LHS) is an instance of
   * ZRefNameList and throws an UnsupportedAstClassException otherwise.
   */
  ZRefNameList getZLHS();

  /**
   * This is a convenience method.
   * It returns the ZExprList if ExprList (RHS) is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  ZExprList getZRHS();
