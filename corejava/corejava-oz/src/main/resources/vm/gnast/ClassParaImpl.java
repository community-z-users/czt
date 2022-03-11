
  public net.sourceforge.czt.z.ast.ZName getClassName()
  {
	  net.sourceforge.czt.z.ast.Name declName = getName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.ZExprList getInheritedExpr()
  {
	  net.sourceforge.czt.z.ast.ExprList exprList = getInheritedClass();
    if (exprList instanceof net.sourceforge.czt.z.ast.ZExprList) {
      return ((net.sourceforge.czt.z.ast.ZExprList) exprList).getExpr();
    }
    final String message = "Expected the default (Z) implementation of ExprList" +
      " but found " + String.valueOf(exprList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

