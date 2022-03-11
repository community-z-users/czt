
  public net.sourceforge.czt.z.ast.ZExprList getZActuals()
  {
    net.sourceforge.czt.z.ast.ExprList el = getActuals();
    if (el instanceof net.sourceforge.czt.z.ast.ZExprList) {
      return (net.sourceforge.czt.z.ast.ZExprList) el;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(el);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
