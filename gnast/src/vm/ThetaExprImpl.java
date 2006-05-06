  public ZStrokeList getZStrokeList()
  {
    StrokeList strokeList = getStrokeList();
    if (strokeList instanceof ZStrokeList) {
      return (ZStrokeList) strokeList;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
