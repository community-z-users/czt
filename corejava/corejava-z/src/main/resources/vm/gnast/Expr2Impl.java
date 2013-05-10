  public net.sourceforge.czt.z.ast.Expr getLeftExpr()
  {
	  net.sourceforge.czt.z.ast.Expr result = null;
    if (getExpr().size() > 0) {
      result = getExpr().get(0);
    }
    return result;
  }

  public void setLeftExpr(net.sourceforge.czt.z.ast.Expr expr)
  {
    if (getExpr().size() > 0) {
      getExpr().set(0, expr);
    }
    else {
      getExpr().add(expr);
    }
  }

  public net.sourceforge.czt.z.ast.Expr getRightExpr()
  {
	  net.sourceforge.czt.z.ast.Expr result = null;
    if (getExpr().size() > 1) {
      result = getExpr().get(1);
    }
    return result;
  }

  public void setRightExpr(net.sourceforge.czt.z.ast.Expr expr)
  {
    if (getExpr().size() == 0) {
      getExpr().add(null);
    }
    if (getExpr().size() > 1) {
      getExpr().set(1, expr);
    }
    else {
      getExpr().add(expr);
    }
  }
