
  /**
   * This is a convenience method.
   * It returns the list of declarations if the ExprList is an instance of
   * ZExprList and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.base.ast.ListTerm<Expr> getExpr()
  {
    ExprList exprList = getExprList();
    if (exprList instanceof ZExprList) {
      return ((ZExprList) exprList).getExpr();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
