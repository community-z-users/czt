
  public boolean isEquality()
  {
    final boolean mixfix = getMixfix().booleanValue();
    final Expr firstExpr = getLeftExpr();
    final Expr secondExpr = getRightExpr();
    if (mixfix && secondExpr instanceof SetExpr) {
      SetExpr setExpr = (SetExpr) secondExpr;
      if (setExpr.getExpr().size() == 1) {
        return true;
      }
    }
    return false;
  }
