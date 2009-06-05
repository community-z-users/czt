  public ZStrokeList getZStrokeList()
  {
    StrokeList strokeList = getStrokeList();
    if (strokeList instanceof ZStrokeList) {
      return (ZStrokeList) strokeList;
    }
    final String message = "Expected the default (Z) implementation of StrokeList" +
      " but found " + String.valueOf(strokeList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
