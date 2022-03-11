  public net.sourceforge.czt.circus.ast.CircusFieldList getCircusFieldList()
  {
    net.sourceforge.czt.circus.ast.FieldList fl = getFieldList();
    if (fl instanceof net.sourceforge.czt.circus.ast.CircusFieldList) {
      return (net.sourceforge.czt.circus.ast.CircusFieldList) fl;
    }
    final String message = "Expected the default (Circus) implementation of FieldList" +
      " but found " + String.valueOf(fl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
