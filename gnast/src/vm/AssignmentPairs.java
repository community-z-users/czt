  /**
   * This is a convenience method.
   * It returns the ZNameList if NameList (LHS) is an instance of
   * ZNameList and throws an UnsupportedAstClassException otherwise.
   */
  ZNameList getZLHS();

  /**
   * This is a convenience method.
   * It returns the ZExprList if ExprList (RHS) is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  ZExprList getZRHS();
