  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  ZDeclName getClassName();

  /**
   * This is a convenience method.
   * It returns the list of expressions if the ExprList is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.base.ast.ListTerm<Expr> getInheritedExpr();

