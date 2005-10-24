  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName (ChanName) is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  ZRefName getZChanName();

  /**
   * This is a convenience method.
   * It returns the ZExprList if ExprList (GenActuals) is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  ZExprList getZGenActuals();
