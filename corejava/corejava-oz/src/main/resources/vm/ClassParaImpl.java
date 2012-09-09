
  public ZName getClassName()
  {
    Name declName = getName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public ZExprList getInheritedExpr()
  {
    ExprList exprList = getInheritedClass();
    if (exprList instanceof ZExprList) {
      return ((ZExprList) exprList).getExpr();
    }
    final String message = "Expected the default (Z) implementation of ExprList" +
      " but found " + String.valueOf(exprList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

