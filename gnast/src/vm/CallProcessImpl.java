
  public net.sourceforge.czt.z.ast.ZExprList getZActuals()
  {
    net.sourceforge.czt.z.ast.ExprList el = getActuals();
    if (el instanceof net.sourceforge.czt.z.ast.ZExprList) {
      return (net.sourceforge.czt.z.ast.ZExprList) el;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
