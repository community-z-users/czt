
  public net.sourceforge.czt.z.ast.ZNameList getZGenFormals()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getGenFormals();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
