  /**
   * This is a convenience method.
   * It returns the ZDeclName if DeclName is an instance of
   * ZDeclName and throws an UnsupportedAstClassException otherwise.
   */
  public ZDeclName getClassName()
  {
    DeclName declName = getDeclName();
    if (declName instanceof ZDeclName) {
      return (ZDeclName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  /**
   * This is a convenience method.
   * It returns the list of declarations if the ExprList is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.base.ast.ListTerm<Expr> getInheritedExpr()
  {
    ExprList exprList = getInheritedClass();
    if (exprList instanceof ZExprList) {
      return ((ZExprList) exprList).getExpr();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

