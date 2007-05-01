
  public net.sourceforge.czt.z.ast.ZNameList getZGenFormals()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getGenFormals();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }


  public net.sourceforge.czt.z.ast.ZName getZName()
  {
    net.sourceforge.czt.z.ast.Name declName = getName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
