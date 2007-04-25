  public net.sourceforge.czt.z.ast.ZParaList getZLocalPara()
  {
    net.sourceforge.czt.z.ast.ParaList pl = getLocalPara();
    if (pl instanceof net.sourceforge.czt.z.ast.ZParaList) {
      return (net.sourceforge.czt.z.ast.ZParaList) pl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.ZParaList getZOnTheFlyPara()
  {
    net.sourceforge.czt.z.ast.ParaList pl = getOnTheFlyPara();
    if (pl instanceof net.sourceforge.czt.z.ast.ZParaList) {
      return (net.sourceforge.czt.z.ast.ZParaList) pl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
