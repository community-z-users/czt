  public net.sourceforge.czt.z.ast.Expr getLeftExpr()
  {
	  net.sourceforge.czt.z.ast.Expr result = null;
    if (getExpr().size() > 0) {
      result = getExpr().get(0);
    }
    return result;
  }

  public net.sourceforge.czt.z.ast.Expr getRightExpr()
  {
	  net.sourceforge.czt.z.ast.Expr result = null;
    if (getExpr().size() > 1) {
      result = getExpr().get(1);
    }
    return result;
  }
