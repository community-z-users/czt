
  public net.sourceforge.czt.z.ast.ZName getProcessZName()
  {
    net.sourceforge.czt.z.ast.Name declName = getProcessName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
