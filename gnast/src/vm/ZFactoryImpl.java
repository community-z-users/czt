
  private java.util.List list(Object o)
  {
    java.util.List result = new java.util.ArrayList();
    result.add(o);
    return result;
  }

  private java.util.List list(Object first, Object second)
  {
    java.util.List result = new java.util.ArrayList();
    result.add(first);
    result.add(second);
    return result;
  }

  public MemPred createEquality(Expr left, Expr right)
  {
    return createMemPred(left, createSetExpr(list(right)), Boolean.TRUE);
  }
  
  public ProdExpr createProdExpr(Expr left, Expr right)
  {
    return createProdExpr(list(left, right));
  }

  public RefName createRefName(DeclName declName)
  {
    return createRefName(declName.getWord(), declName.getStroke(), declName);
  }

  public TupleExpr createTupleExpr(Expr left, Expr right)
  {
    return createTupleExpr(list(left, right));
  }
