  public Expr getLeftExpr()
  {
    Expr result = null;
    if (getExpr().size() > 0) {
      result = getExpr().get(0);
    }
    return result;
  }

  public Expr getRightExpr()
  {
    Expr result = null;
    if (getExpr().size() > 1) {
      result = getExpr().get(1);
    }
    return result;
  }
