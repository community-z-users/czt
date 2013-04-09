  public net.sourceforge.czt.z.ast.ZStrokeList getZStrokeList()
  {
	  net.sourceforge.czt.z.ast.StrokeList strokeList = getStrokeList();
    if (strokeList instanceof net.sourceforge.czt.z.ast.ZStrokeList) {
      return (net.sourceforge.czt.z.ast.ZStrokeList) strokeList;
    }
    final String message = "Expected the default (Z) implementation of StrokeList" +
      " but found " + String.valueOf(strokeList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
