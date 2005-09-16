  /**
   * This is a convenience method.
   * It returns the list of rename pairs if the RenameList is an instance of
   * ZRenameList and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.base.ast.ListTerm<NewOldPair> getRenamings()
  {
    RenameList renameList = getRenameList();
    if (renameList instanceof ZRenameList) {
      return ((ZRenameList) renameList).getNewOldPair();
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
