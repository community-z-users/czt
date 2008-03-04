  public net.sourceforge.czt.circus.ast.CircusCommunicationList getCircusCommunicationList()
  {
    net.sourceforge.czt.circus.ast.CommunicationList cl = getCommunicationList();
    if (cl instanceof net.sourceforge.czt.circus.ast.CircusCommunicationList) {
      return (net.sourceforge.czt.circus.ast.CircusCommunicationList) cl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }