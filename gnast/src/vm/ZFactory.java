
  /**
   * Creates a MemPred that represents equality
   * between the two given expressions.
   */
  MemPred createEquality(Expr left, Expr right);

  /**
   * Creates a binary ProdExpr.
   */
  ProdExpr createProdExpr(Expr left, Expr right);

  /**
   * Creates a RefName which refers to the given DeclName.
   */
  RefName createRefName(DeclName declName);

  /**
   * Creates a pair, that is a tuple expression with exactly
   * two elements.
   */
  TupleExpr createTupleExpr(Expr left, Expr right);

