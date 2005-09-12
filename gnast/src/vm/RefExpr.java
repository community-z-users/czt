
  /**
   * This is a convenience method.
   * It returns the list of expressions if the ExprList is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.base.ast.ListTerm<Expr> getExpr();

  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  ZRefName getZRefName();
