
  /**
   * Creates a list of size one with the given object as element.
   */
  public java.util.List list(Object o)
  {
    java.util.List result = new java.util.ArrayList();
    result.add(o);
    return result;
  }

  /**
   * Creates a list with the two objects as elements.
   */
  public java.util.List list(Object first, Object second)
  {
    java.util.List result = new java.util.ArrayList();
    result.add(first);
    result.add(second);
    return result;
  }

  /**
   * Creates a member predicate that represents equality
   * between the two given expressions.
   */
  public MemPred createEquality(Expr left, Expr right)
  {
    return createMemPred(left, createSetExpr(list(right)), Boolean.TRUE);
  }

  /**
   * Creates a binary product expression.
   */
  public ProdExpr createProdExpr(Expr left, Expr right)
  {
    return createProdExpr(list(left, right));
  }

  /**
   * Creates a referencing name that refers to the given
   * declaring name.
   */
  public RefName createRefName(DeclName declName)
  {
    return createRefName(declName.getWord(), declName.getStroke(), declName);
  }

  /**
   * Creates a pair, that is a tuple expression with two elements.
   */
  public TupleExpr createTupleExpr(Expr left, Expr right)
  {
    return createTupleExpr(list(left, right));
  }



  
