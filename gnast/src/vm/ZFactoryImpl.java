
  private java.util.List list(Object o)
  {
    java.util.List result = new java.util.ArrayList();
    result.add(o);
    return result;
  }

  public MemPred createEquality(Expr expr1, Expr expr2)
  {
    return createMemPred(expr1, createSetExpr(list(expr2)), Boolean.TRUE);
  }
  
