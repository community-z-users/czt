
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
   * Creates a horizontal definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * expression and with Box set to OmitBox.
   *
   * @param declName name of the schema.
   * @param expr an expression.
   */
  public AxPara createHorizontalDef(DeclName declName, Expr expr)
  {
    return createHorizontalDef(declName, null, expr);
  }

  /**
   * Creates a generic horizontal definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * expression and with Box set to OmitBox.
   *
   * @param declName name of the schema.
   * @param formals a list of DeclName, the formal parameters.
   * @param expr an expression.
   */
  public AxPara createHorizontalDef(DeclName declName,
                                    java.util.List formals,
                                    Expr expr)
  {
    ConstDecl constDecl = createConstDecl(declName, expr);
    SchText schText = createSchText(list(constDecl), null);
    return createAxPara(formals, schText, Box.OmitBox);
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
   * Creates a number expression with the given value.
   */
  public NumExpr createNumExpr(int value)
  {
    return createNumExpr(java.math.BigInteger.valueOf(value));
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
   * Creates a schema definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * schema text and with Box set to SchBox.
   *
   * @param declName name of the schema.
   * @param schemaText the schema text.
   */
  public AxPara createSchema(DeclName declName, SchText schemaText)
  {
    return createSchema(declName, null, schemaText);
  }

  /**
   * Creates a generic schema definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * schema text and with Box set to SchBox.
   *
   * @param formals a list of DeclName, the formal parameters.
   * @param declName name of the schema.
   * @param schemaText the schema text.
   */
  public AxPara createSchema(DeclName declName,
                             java.util.List formals,
                             SchText schemaText)
  {
    ConstDecl constDecl = createConstDecl(declName, createSchExpr(schemaText));
    SchText schText = createSchText(list(constDecl), null);
    return createAxPara(formals, schText, Box.SchBox);
  }

  /**
   * <p>Creates a sequence, that is a set of pairs of position
   * (starting from 1) and corresponding component expression.
   * This applies rule 12.2.12 of the Z standard to a list of
   * expressions.</p>
   *
   * <p>More formally, a list
   * <code>e_1, ..., e_n</code> of expressions is transformed into
   * the set <code>\{ (1, e_1), ... , (n, e_n) \}</code>.
   * </p>
   *
   * @param exprList a list of expressions (Expr).
   */
  public SetExpr createSequence(java.util.List exprList)
  {
    java.util.List tupleList = new java.util.ArrayList(exprList.size());
    int count = 1;
    for (java.util.Iterator i = exprList.iterator(); i.hasNext(); count++) {
      tupleList.add(createTupleExpr(createNumExpr(count), (Expr) i.next()));
    }
    return createSetExpr(tupleList);
  }

  /**
   * Creates a pair, that is a tuple expression with two elements.
   */
  public TupleExpr createTupleExpr(Expr left, Expr right)
  {
    return createTupleExpr(list(left, right));
  }
