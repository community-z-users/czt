
  public net.sourceforge.czt.z.ast.ZNameList getZLHS()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getLHS();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(rnl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.ZExprList getZRHS()
  {
    net.sourceforge.czt.z.ast.ExprList expr = getRHS();
    if (expr instanceof net.sourceforge.czt.z.ast.ZExprList) {
      return (net.sourceforge.czt.z.ast.ZExprList) expr;
    }
    final String message = "Expected the default (Z) implementation of ExprList" +
      " but found " + String.valueOf(expr);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

