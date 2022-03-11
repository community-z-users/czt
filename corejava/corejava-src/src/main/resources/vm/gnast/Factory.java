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
  public <E> java.util.List<E> list(@SuppressWarnings("unchecked") E... elems)
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
  public net.sourceforge.czt.z.ast.ApplExpr createApplication(net.sourceforge.czt.z.ast.Name refName, net.sourceforge.czt.z.ast.Expr expr)
  {
    return createApplExpr(createRefExpr(refName), expr, Boolean.FALSE);
  }

  /**
   * Creates a ZName with the given word and strokes and
   * id set to <code>null</code>.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.ZName createZName(String word, net.sourceforge.czt.z.ast.StrokeList strokes)
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
  public net.sourceforge.czt.z.ast.ZName createZName(String decorword)
  {
    net.sourceforge.czt.z.ast.ZStrokeList strokes = createZStrokeList();
    final String word = getWordAndStrokes(decorword, strokes);
    return createZName(word, strokes, null);
  }

  public String getWordAndStrokes(String decorword,
                                  net.sourceforge.czt.z.ast.ZStrokeList strokes)
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
  public net.sourceforge.czt.z.ast.MemPred createEquality(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.ZExprList zExprList = createZExprList();
    zExprList.add(right);
    return createMemPred(left, createSetExpr(zExprList), Boolean.TRUE);
  }

  /**
   * Creates a function operator application, that is an ApplExpr
   * with mixfix set to <code>true</code>.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.ApplExpr createFunOpAppl(net.sourceforge.czt.z.ast.Name refName, net.sourceforge.czt.z.ast.Expr expr)
  {
    return createApplExpr(createRefExpr(refName), expr, Boolean.TRUE);
  }

  /**
   * Creates a generic instantiation expression, that is a RefExpr
   * with mixfix set to <code>false</code>.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.RefExpr createGenInst(net.sourceforge.czt.z.ast.Name refName,
                               java.util.List<? extends net.sourceforge.czt.z.ast.Expr> exprs)
  {
    net.sourceforge.czt.z.ast.ZExprList zExprList = createZExprList(exprs);
    return createRefExpr(refName, zExprList, Boolean.FALSE);
  }

  /**
   * Creates a generic operator application, that is a RefExpr
   * with mixfix set to <code>true</code>.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.RefExpr createGenOpApp(net.sourceforge.czt.z.ast.Name refName,
                                java.util.List<? extends net.sourceforge.czt.z.ast.Expr> exprs)
  {
    net.sourceforge.czt.z.ast.ZExprList zExprList = createZExprList(exprs);
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
  public net.sourceforge.czt.z.ast.AxPara createHorizontalDef(net.sourceforge.czt.z.ast.Name declName, net.sourceforge.czt.z.ast.Expr expr)
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
  public net.sourceforge.czt.z.ast.AxPara createHorizontalDef(net.sourceforge.czt.z.ast.Name declName,
                                    java.util.List<? extends net.sourceforge.czt.z.ast.Name> formals,
                                    net.sourceforge.czt.z.ast.Expr expr)
  {
    net.sourceforge.czt.z.ast.ZNameList zdnl = createZNameList();
    if (formals != null) {
      zdnl.addAll(formals);
    }
    net.sourceforge.czt.z.ast.Decl decl = createConstDecl(declName, expr);
    net.sourceforge.czt.z.ast.SchText schText = createZSchText(createZDeclList(list(decl)), null);
    return createAxPara(zdnl, schText, net.sourceforge.czt.z.ast.Box.OmitBox);
  }

  /**
   * Creates a member predicate for a given referencing name and
   * an expression, that is a MemPred with mixfix set to <code>false</code>.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.MemPred createMemPred(net.sourceforge.czt.z.ast.Name refName, net.sourceforge.czt.z.ast.Expr expr)
  {
    return createMemPred(createRefExpr(refName), expr, Boolean.FALSE);
  }
  
  public net.sourceforge.czt.z.ast.Pred createSetMembership(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    return createMemPred(left, right, Boolean.FALSE);
  }

  /**
   * Creates a number expression with the given value.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.NumExpr createNumExpr(int value)
  {
    return factory_.createNumExpr(createZNumeral(value));
  }

  /**
   * Creates a number expression with the given value.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.NumExpr createNumExpr(java.math.BigInteger bigInt)
  {
    return createNumExpr(factory_.createZNumeral(bigInt));
  }

  public net.sourceforge.czt.z.ast.ZNumeral createZNumeral(int value)
  {
    return factory_.createZNumeral(java.math.BigInteger.valueOf(value));
  }

  /**
   * Creates a binary product expression.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.ProdExpr createProdExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    return createProdExpr(createZExprList(list(left, right)));
  }

  public net.sourceforge.czt.z.ast.RefExpr createRefExpr(net.sourceforge.czt.z.ast.Name refName,
                               net.sourceforge.czt.z.ast.ZExprList zExprList,
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
  public net.sourceforge.czt.z.ast.RefExpr createRefExpr(net.sourceforge.czt.z.ast.Name refName)
  {
    return createRefExpr(refName, createZExprList(), Boolean.FALSE);
  }

  /**
   * Creates a referencing name that refers to the given
   * declaring name, i.e., just copies the given ZName.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.ZName createZName(net.sourceforge.czt.z.ast.ZName declName)
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
  public net.sourceforge.czt.z.ast.MemPred createRelOpAppl(net.sourceforge.czt.z.ast.Expr expr, net.sourceforge.czt.z.ast.Name refName)
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
  public net.sourceforge.czt.z.ast.AxPara createSchema(net.sourceforge.czt.z.ast.Name declName, net.sourceforge.czt.z.ast.SchText schemaText)
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
  public net.sourceforge.czt.z.ast.AxPara createSchema(net.sourceforge.czt.z.ast.Name declName,
                             java.util.List<? extends net.sourceforge.czt.z.ast.Name> formals,
                             net.sourceforge.czt.z.ast.SchText schemaText)
  {
    net.sourceforge.czt.z.ast.ZNameList zdnl = createZNameList();
    if (formals != null) {
      zdnl.addAll(formals);
    }
    net.sourceforge.czt.z.ast.Decl decl = createConstDecl(declName, createSchExpr(schemaText));
    net.sourceforge.czt.z.ast.SchText schText = createZSchText(createZDeclList(list(decl)), null);
    return createAxPara(zdnl, schText, net.sourceforge.czt.z.ast.Box.SchBox);
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
  public net.sourceforge.czt.z.ast.SetExpr createSequence(java.util.List<? extends net.sourceforge.czt.z.ast.Expr> exprList)
  {
    net.sourceforge.czt.z.ast.ZExprList zExprList = createZExprList();
    int count = 1;
    for (java.util.Iterator<? extends net.sourceforge.czt.z.ast.Expr> i = exprList.iterator();
         i.hasNext(); count++) {
      zExprList.add(createTupleExpr(createNumExpr(count), i.next()));
    }
    return createSetExpr(zExprList);
  }

  /**
   * Creates a pair, that is a tuple expression with two elements.
   * This is a convenience method.
   */
  public net.sourceforge.czt.z.ast.TupleExpr createTupleExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
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

  public net.sourceforge.czt.z.ast.NumStroke createNumStroke(int value)
  {
    net.sourceforge.czt.base.ast.Digit digit =
      net.sourceforge.czt.base.ast.Digit.fromValue(value);
    return createNumStroke(digit);
  }

  public net.sourceforge.czt.z.ast.LocAnn createLocAnn(String source, Integer line, Integer col)
  {
    return createLocAnn(source, line, col, null, null);
  }

  public net.sourceforge.czt.z.ast.LocAnn createLocAnn(String source,
                             Integer line, Integer col,
                             Integer start, Integer length)
  {
    return createLocAnn(source,
                        toBig(line), toBig(col),
                        toBig(start), toBig(length));
  }

  public net.sourceforge.czt.z.ast.AndExpr createAndExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.AndExpr result = createAndExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.AndPred createAndPred(net.sourceforge.czt.z.ast.Pred left, net.sourceforge.czt.z.ast.Pred right, net.sourceforge.czt.z.ast.And and)
  {
    net.sourceforge.czt.z.ast.AndPred result = createAndPred();
    result.getPred().add(left);
    result.getPred().add(right);
    result.setAnd(and);
    return result;
  }

  public net.sourceforge.czt.z.ast.ApplExpr createApplExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right, Boolean  mixfix)
  {
    net.sourceforge.czt.z.ast.ApplExpr result = createApplExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    result.setMixfix(mixfix);
    return result;
  }

  public net.sourceforge.czt.z.ast.CompExpr createCompExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.CompExpr result = createCompExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.CondExpr createCondExpr(net.sourceforge.czt.z.ast.Pred pred, net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.CondExpr result = createCondExpr();
    result.setPred(pred);
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.IffExpr createIffExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.IffExpr result = createIffExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.IffPred createIffPred(net.sourceforge.czt.z.ast.Pred left, net.sourceforge.czt.z.ast.Pred right)
  {
    net.sourceforge.czt.z.ast.IffPred result = createIffPred();
    result.getPred().add(left);
    result.getPred().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.ImpliesExpr createImpliesExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.ImpliesExpr result = createImpliesExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.ImpliesPred createImpliesPred(net.sourceforge.czt.z.ast.Pred left, net.sourceforge.czt.z.ast.Pred right)
  {
    net.sourceforge.czt.z.ast.ImpliesPred result = createImpliesPred();
    result.getPred().add(left);
    result.getPred().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.MemPred createMemPred(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right, Boolean mixfix)
  {
    net.sourceforge.czt.z.ast.MemPred result = createMemPred();
    result.getExpr().add(left);
    result.getExpr().add(right);
    result.setMixfix(mixfix);
    return result;
  }

  public net.sourceforge.czt.z.ast.OrExpr createOrExpr(net.sourceforge.czt.z.ast.Expr  left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.OrExpr result = createOrExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.OrPred createOrPred(net.sourceforge.czt.z.ast.Pred  left, net.sourceforge.czt.z.ast.Pred right)
  {
    net.sourceforge.czt.z.ast.OrPred result = createOrPred();
    result.getPred().add(left);
    result.getPred().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.PipeExpr createPipeExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.PipeExpr result = createPipeExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.ProjExpr createProjExpr(net.sourceforge.czt.z.ast.Expr left, net.sourceforge.czt.z.ast.Expr right)
  {
    net.sourceforge.czt.z.ast.ProjExpr result = createProjExpr();
    result.getExpr().add(left);
    result.getExpr().add(right);
    return result;
  }

  public net.sourceforge.czt.z.ast.NewOldPair createNewOldPair(net.sourceforge.czt.z.ast.Name newName, net.sourceforge.czt.z.ast.Name oldName)
  {
    net.sourceforge.czt.z.ast.NewOldPair result = createNewOldPair();
    result.getName().add(newName);
    result.getName().add(oldName);
    return result;
  }