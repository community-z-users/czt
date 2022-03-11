  public net.sourceforge.czt.z.ast.ZParaList getZParaList()
  {
    net.sourceforge.czt.z.ast.ParaList pl = getParaList();
    if (pl instanceof net.sourceforge.czt.z.ast.ZParaList) {
      return (net.sourceforge.czt.z.ast.ZParaList) pl;
    }
    final String message = "Expected the default (Z) implementation of ParaList" +
      " but found " + String.valueOf(pl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
