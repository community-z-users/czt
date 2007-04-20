
  public net.sourceforge.czt.z.ast.ZNameList getZFrame()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getFrame();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
