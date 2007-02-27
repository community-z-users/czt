  public Expr getLeftExpr()
  {
    Expr result = null;
    if (getExpr().size() > 0) {
      result = getExpr().get(0);
    }
    return result;
  }

  public void setLeftExpr(Expr expr)
  {
    if (getExpr().size() > 0) {
      getExpr().set(0, expr);
    }
    else {
      getExpr().add(expr);
    }
  }

  public Expr getRightExpr()
  {
    Expr result = null;
    if (getExpr().size() > 1) {
      result = getExpr().get(1);
    }
    return result;
  }

  public void setRightExpr(Expr expr)
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
