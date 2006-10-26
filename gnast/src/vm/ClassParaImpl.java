
  public ZName getClassName()
  {
    Name declName = getName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public ZExprList getInheritedExpr()
  {
    ExprList exprList = getInheritedClass();
    if (exprList instanceof ZExprList) {
      return ((ZExprList) exprList).getExpr();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

