
  public net.sourceforge.czt.z.ast.ZNameList getZGenFormals()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getGenFormals();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(rnl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }


  public net.sourceforge.czt.z.ast.ZName getZName()
  {
    net.sourceforge.czt.z.ast.Name declName = getName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
