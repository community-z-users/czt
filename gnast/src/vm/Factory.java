
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
   * Creates an application (Expr followed by Expr in the syntax),
   * that is an ApplExpr with mixfix set to <code>false</code>.
   */
  public ApplExpr createApplication(RefName refName, Expr expr)
  {
    return createApplExpr(createRefExpr(refName), expr, Boolean.FALSE);
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
   * Creates a function operator application, that is an ApplExpr
   * with mixfix set to <code>true</code>.
   */
  public ApplExpr createFunOpAppl(RefName refName, Expr expr)
  {
    return createApplExpr(createRefExpr(refName), expr, Boolean.TRUE);
  }

  /**
   * Creates a generic instantiation expression, that is a RefExpr
   * with mixfix set to <code>false</code>.
   */
  public RefExpr createGenInst(RefName refName, java.util.List exprs)
  {
    return createRefExpr(refName, exprs, Boolean.FALSE);
  }

  /**
   * Creates a generic operator application, that is a RefExpr
   * with mixfix set to <code>true</code>.
   */
  public RefExpr createGenOpApp(RefName refName, java.util.List exprs)
  {
    return createRefExpr(refName, exprs, Boolean.TRUE);
  }

  /**
   * Creates a member predicate for a given referencing name and
   * an expression, that is a MemPred with mixfix set to <code>false</code>.
   */ 
  public MemPred createMemPred(RefName refName, Expr expr)
  {
    return createMemPred(createRefExpr(refName), expr, Boolean.FALSE);
  }

  /**
   * Creates a binary product expression.
   */
  public ProdExpr createProdExpr(Expr left, Expr right)
  {
    return createProdExpr(list(left, right));
  }

  /**
   * Creates a reference (expression) to the given name.
   * The mixfix child of the returned reference expression
   * is <code>false</code> and the list of expressions is empty.
   */
  public RefExpr createRefExpr(RefName refName)
  {
    return createRefExpr(refName, null, Boolean.FALSE);
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
   * Creates a relation operator application, that is a MemPred
   * with mixfix set to <code>true</code>.
   */
  public MemPred createRelOpAppl(Expr expr, RefName refName)
  {
    return createMemPred(expr, createRefExpr(refName), Boolean.TRUE);
  }

  /**
   * Creates a pair, that is a tuple expression with two elements.
   */
  public TupleExpr createTupleExpr(Expr left, Expr right)
  {
    return createTupleExpr(list(left, right));
  }
