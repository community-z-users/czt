
  public net.sourceforge.czt.z.ast.ZNameList getZGenFormals()
  {
    if (getNameList().size() > 0) {
      net.sourceforge.czt.z.ast.NameList rnl = getNameList().get(0);
      if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
        return (net.sourceforge.czt.z.ast.ZNameList) rnl;
      }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.ZNameList getZChannelNameList()
  {
    if (getNameList().size() > 1) {
      net.sourceforge.czt.z.ast.NameList rnl = getNameList().get(1);
      if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
        return (net.sourceforge.czt.z.ast.ZNameList) rnl;
      }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
