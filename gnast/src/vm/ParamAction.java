
  /**
   * <p>
   * This method characterises parameterised commands and actions according to the
   * expected (specific and disjoint) structure both have, yet they share the same
   * AST class due to their similar nature and to minimize AST numbers. This choice
   * is similar to AxPara in Z, which represents various Z boxes.
   * </p>
   * <p>
   * The protocol is as follows: parameterised commands MUST have a CircusCommand
   * as its inner term, and VarDecl and QualifiedDecl are allowed; whereas parameterised 
   * actions have a CircusAction as its inner term, and only VarDecl is allowed. This
   * method only check for the inner term, whereas other tools (i.e. parser and typechecker)
   * check which declaration is allowed
   * </p>
   * @return true if this is a parameterised command; false for parameterised action
   */
  boolean isParamCommand();
