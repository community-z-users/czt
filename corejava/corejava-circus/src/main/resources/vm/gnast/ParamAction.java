  /**
   * <p>
   * This method characterises parameterised commands and actions according to the
   * expected (specific and disjoint) structure both have, yet they share the same
   * AST class due to their similar nature and to minimize AST numbers. This choice
   * is similar to AxPara in Z, which represents various Z boxes.
   * </p>
   * <p>
   * The protocol is as follows: parameterised commands MUST have a ZDeclList with
   * QualifiedDecl only; whereas parameterised actions only allow VarDecl. 
   * </p>
   * @return true if this is a parameterised command; false for parameterised action
   */
  boolean isParamCommand();
