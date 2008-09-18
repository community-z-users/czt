  /**
   * Creates an empty list of the given element type.
   * This is a convenience method.
   */
  public <E> java.util.List<E> list()
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    return result;
  }
  

  /**
   * Creates a list with the given elements.
   * This is a convenience method.
   */
  public <E> java.util.List<E> list(E... elems)
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }

  /**
   * Creates an application (Expr followed by Expr in the syntax),
   * that is an ApplExpr with mixfix set to <code>false</code>.
   * This is a convenience method.
   */
  public ApplExpr createApplication(Name refName, Expr expr)
  {
    return createApplExpr(createRefExpr(refName), expr, Boolean.FALSE);
  }

  /**
   * Creates a ZName with the given word and strokes and
   * id set to <code>null</code>.
   * This is a convenience method.
   */
  public ZName createZName(String word, StrokeList strokes)
  {
    return createZName(word, strokes, null);
  }

  /**
   * Creates a ZName from a decorword, that is a string that
   * may contain strokes at the end.
   * The strokes are extracted from the end and the resulting
   * name is returned.
   * This is a convenience method.
   */
  public ZName createZName(String decorword)
  {
    ZStrokeList strokes = createZStrokeList();
    final String word = getWordAndStrokes(decorword, strokes);
    return createZName(word, strokes, null);
  }

  public String getWordAndStrokes(String decorword,
                                  ZStrokeList strokes)
  {
    net.sourceforge.czt.z.util.ZChar[] zchars =
      net.sourceforge.czt.z.util.ZChar.toZChars(decorword);
    int i;
    for (i = zchars.length - 1; i >= 0; i--) {
      net.sourceforge.czt.z.util.ZChar zchar = zchars[i];
      if (net.sourceforge.czt.z.util.ZChar.INSTROKE.equals(zchar)) {
        strokes.add(0, createInStroke());
      }
      else if (net.sourceforge.czt.z.util.ZChar.OUTSTROKE.equals(zchar)) {
        strokes.add(0, createOutStroke());
      }
      else if (net.sourceforge.czt.z.util.ZChar.PRIME.equals(zchar)) {
        strokes.add(0, createNextStroke());
      }
      else if (i >= 2 &&
          net.sourceforge.czt.z.util.ZChar.NW.equals(zchar) &&
          net.sourceforge.czt.z.util.ZChar.isDigit(zchars[i - 1]) &&
          net.sourceforge.czt.z.util.ZChar.SE.equals(zchars[i - 2])) {
        net.sourceforge.czt.base.ast.Digit digit =
          net.sourceforge.czt.base.util.CztDatatypeConverter.parseDigit(zchars[i - 1].toString());
        strokes.add(0, createNumStroke(digit));
        i = i - 2;
      }
      else {
        break;
      }
    }
    StringBuffer result = new StringBuffer();
    for (int j = 0; j <= i; j++) {
      result.append(zchars[j].toString());
    }
    return result.toString();
  }

  /**
   * Creates a member predicate that represents equality
   * between the two given expressions.
   * This is a convenience method.
   */
  public MemPred createEquality(Expr left, Expr right)
  {
    ZExprList zExprList = createZExprList();
    zExprList.add(right);
    return createMemPred(left, createSetExpr(zExprList), Boolean.TRUE);
  }

  /**
   * Creates a function operator application, that is an ApplExpr
   * with mixfix set to <code>true</code>.
   * This is a convenience method.
   */
  public ApplExpr createFunOpAppl(Name refName, Expr expr)
  {
    return createApplExpr(createRefExpr(refName), expr, Boolean.TRUE);
  }

  /**
   * Creates a generic instantiation expression, that is a RefExpr
   * with mixfix set to <code>false</code>.
   * This is a convenience method.
   */
  public RefExpr createGenInst(Name refName,
                               java.util.List<? extends Expr> exprs)
  {
    ZExprList zExprList = createZExprList(exprs);
    return createRefExpr(refName, zExprList, Boolean.FALSE);
  }

  /**
   * Creates a generic operator application, that is a RefExpr
   * with mixfix set to <code>true</code>.
   * This is a convenience method.
   */
  public RefExpr createGenOpApp(Name refName,
                                java.util.List<? extends Expr> exprs)
  {
    ZExprList zExprList = createZExprList(exprs);
    return createRefExpr(refName, zExprList, Boolean.TRUE);
  }

  /**
   * Creates a horizontal definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * expression and with Box set to OmitBox.
   * This is a convenience method.
   *
   * @param declName name of the schema.
   * @param expr an expression.
   */
  public AxPara createHorizontalDef(Name declName, Expr expr)
  {
    return createHorizontalDef(declName, null, expr);
  }

  /**
   * Creates a generic horizontal definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * expression and with Box set to OmitBox.
   * This is a convenience method.
   *
   * @param declName name of the schema.
   * @param formals a list of Name, the formal parameters.
   * @param expr an expression.
   */
  public AxPara createHorizontalDef(Name declName,
                                    java.util.List<? extends Name> formals,
                                    Expr expr)
  {
    ZNameList zdnl = createZNameList();
    if (formals != null) {
      zdnl.addAll(formals);
    }
    Decl decl = createConstDecl(declName, expr);
    SchText schText = createZSchText(createZDeclList(list(decl)), null);
    return createAxPara(zdnl, schText, Box.OmitBox);
  }

  /**
   * Creates a member predicate for a given referencing name and
   * an expression, that is a MemPred with mixfix set to <code>false</code>.
   * This is a convenience method.
   */
  public MemPred createMemPred(Name refName, Expr expr)
  {
    return createMemPred(createRefExpr(refName), expr, Boolean.FALSE);
  }

  /**
   * Creates a number expression with the given value.
   * This is a convenience method.
   */
  public NumExpr createNumExpr(int value)
  {
    return factory_.createNumExpr(createZNumeral(value));
  }

  /**
   * Creates a number expression with the given value.
   * This is a convenience method.
   */
  public NumExpr createNumExpr(java.math.BigInteger bigInt)
  {
    return createNumExpr(factory_.createZNumeral(bigInt));
  }

  public ZNumeral createZNumeral(int value)
  {
    return factory_.createZNumeral(java.math.BigInteger.valueOf(value));
  }

  /**
   * Creates a binary product expression.
   * This is a convenience method.
   */
  public ProdExpr createProdExpr(Expr left, Expr right)
  {
    return createProdExpr(createZExprList(list(left, right)));
  }

  public RefExpr createRefExpr(Name refName,
                               ZExprList zExprList,
                               Boolean mixfix)
  {
    return factory_.createRefExpr(refName, zExprList, mixfix, false);
  }

  /**
   * Creates a reference (expression) to the given name.
   * The mixfix child of the returned reference expression
   * is <code>false</code> and the list of expressions is empty.
   * This is a convenience method.
   */
  public RefExpr createRefExpr(Name refName)
  {
    return createRefExpr(refName, createZExprList(), Boolean.FALSE);
  }

  /**
   * Creates a referencing name that refers to the given
   * declaring name, i.e., just copies the given ZName.
   * This is a convenience method.
   */
  public ZName createZName(ZName declName)
  {
    return createZName(declName.getWord(),
                       declName.getStrokeList(),
                       declName.getId());
  }

  /**
   * Creates a relation operator application, that is a MemPred
   * with mixfix set to <code>true</code>.
   * This is a convenience method.
   */
  public MemPred createRelOpAppl(Expr expr, Name refName)
  {
    return createMemPred(expr, createRefExpr(refName), Boolean.TRUE);
  }

  /**
   * Creates a schema definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * schema text and with Box set to SchBox.
   * This is a convenience method.
   *
   * @param declName name of the schema.
   * @param schemaText the schema text.
   */
  public AxPara createSchema(Name declName, SchText schemaText)
  {
    return createSchema(declName, null, schemaText);
  }

  /**
   * Creates a generic schema definition, that is an axiomatic definition
   * containing a constant declaration of the name to the given
   * schema text and with Box set to SchBox.
   * This is a convenience method.
   *
   * @param formals a list of Name, the formal parameters.
   * @param declName name of the schema.
   * @param schemaText the schema text.
   */
  public AxPara createSchema(Name declName,
                             java.util.List<? extends Name> formals,
                             SchText schemaText)
  {
    ZNameList zdnl = createZNameList();
    if (formals != null) {
      zdnl.addAll(formals);
    }
    Decl decl = createConstDecl(declName, createSchExpr(schemaText));
    SchText schText = createZSchText(createZDeclList(list(decl)), null);
    return createAxPara(zdnl, schText, Box.SchBox);
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
   * <p>This is a convenience method.</p>
   *
   * @param exprList a list of expressions (Expr).
   */
  public SetExpr createSequence(java.util.List<? extends Expr> exprList)
  {
    ZExprList zExprList = createZExprList();
    int count = 1;
    for (java.util.Iterator<? extends Expr> i = exprList.iterator();
         i.hasNext(); count++) {
      zExprList.add(createTupleExpr(createNumExpr(count), i.next()));
    }
    return createSetExpr(zExprList);
  }

  /**
   * Creates a pair, that is a tuple expression with two elements.
   * This is a convenience method.
   */
  public TupleExpr createTupleExpr(Expr left, Expr right)
  {
    return createTupleExpr(createZExprList(list(left, right)));
  }

  public java.math.BigInteger toBig(Integer i)
  {
    if (i != null) {
      return java.math.BigInteger.valueOf(i.intValue());
    }
    return null;
  }

  public NumStroke createNumStroke(int value)
  {
    net.sourceforge.czt.base.ast.Digit digit =
      net.sourceforge.czt.base.ast.Digit.fromValue(value);
    return createNumStroke(digit);
  }

  public LocAnn createLocAnn(String source, Integer line, Integer col)
  {
    return createLocAnn(source, line, col, null, null);
  }

  public LocAnn createLocAnn(String source,
                             Integer line, Integer col,
                             Integer start, Integer length)
  {
    return createLocAnn(source,
                        toBig(line), toBig(col),
                        toBig(start), toBig(length));
  }

  public AndExpr createAndExpr(Expr left, Expr right)
  {
    AndExpr result = createAndExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public AndPred createAndPred(Pred left, Pred right, And and)
  {
    AndPred result = createAndPred();
    result.getPred().add(left);
    result.getPred().add(right);
    result.setAnd(and);
    return result;
  }

  public ApplExpr createApplExpr(Expr left, Expr right, Boolean  mixfix)
  {
    ApplExpr result = createApplExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    result.setMixfix(mixfix);
    return result;
  }

  public CompExpr createCompExpr(Expr left, Expr right)
  {
    CompExpr result = createCompExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public CondExpr createCondExpr(Pred pred, Expr left, Expr right)
  {
    CondExpr result = createCondExpr();
    result.setPred(pred);
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public IffExpr createIffExpr(Expr left, Expr right)
  {
    IffExpr result = createIffExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public IffPred createIffPred(Pred left, Pred right)
  {
    IffPred result = createIffPred();
    result.getPred().add(left);
    result.getPred().add(right);
    return result;
  }

  public ImpliesExpr createImpliesExpr(Expr left, Expr right)
  {
    ImpliesExpr result = createImpliesExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public ImpliesPred createImpliesPred(Pred left, Pred right)
  {
    ImpliesPred result = createImpliesPred();
    result.getPred().add(left);
    result.getPred().add(right);
    return result;
  }

  public MemPred createMemPred(Expr left, Expr right, Boolean mixfix)
  {
    MemPred result = createMemPred();
    result.getExpr().add(left);
    result.getExpr().add(right);
    result.setMixfix(mixfix);
    return result;
  }

  public OrExpr createOrExpr(Expr  left, Expr right)
  {
    OrExpr result = createOrExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public OrPred createOrPred(Pred  left, Pred right)
  {
    OrPred result = createOrPred();
    result.getPred().add(left);
    result.getPred().add(right);
    return result;
  }

  public PipeExpr createPipeExpr(Expr left, Expr right)
  {
    PipeExpr result = createPipeExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public ProjExpr createProjExpr(Expr left, Expr right)
  {
    ProjExpr result = createProjExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public NewOldPair createNewOldPair(Name newName, Name oldName)
  {
    NewOldPair result = createNewOldPair();
    result.getName().add(newName);
    result.getName().add(oldName);
    return result;
  }
