
  /**
   * This is a convenience method.
   * It returns the list of declarations if the DeclList is an instance of
   * ZDeclList and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.base.ast.ListTerm<Expr> getExpr()
  {
    ExprList exprList = getExprList();
    if (exprList instanceof ZExprList) {
      return ((ZExprList) exprList).getExpr();
    }
    String message =
      "ZExprList expected but found " + exprList.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefName getZRefName()
  {
    RefName refName = getRefName();
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    String message =
      "ZRefName expected but found " + refName.getClass().toString();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
