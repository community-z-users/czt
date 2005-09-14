
  /**
   * This is a convenience method.
   * It returns the list of declarations if the DeclList is an instance of
   * ZDeclList and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.base.ast.ListTerm<Decl> getDecl()
  {
    DeclList declList = getDeclList();
    if (declList instanceof ZDeclList) {
      return ((ZDeclList) declList).getDecl();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
