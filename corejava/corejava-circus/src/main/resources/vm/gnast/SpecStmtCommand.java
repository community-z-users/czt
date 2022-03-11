  /**
   * This is a convenience method.
   * It returns the ZNameList if NameList is an instance of
   * ZNameList or throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZNameList getZFrame();

  net.sourceforge.czt.z.ast.Pred getPre();
  void setPre(net.sourceforge.czt.z.ast.Pred pred);
  net.sourceforge.czt.z.ast.Pred getPost();
  void setPost(net.sourceforge.czt.z.ast.Pred pred);
