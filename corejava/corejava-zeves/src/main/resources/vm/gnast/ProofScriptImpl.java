
  public net.sourceforge.czt.z.ast.ZName getZName()
  {
    net.sourceforge.czt.z.ast.Name proofName = getName();
    if (proofName instanceof net.sourceforge.czt.z.ast.ZName) {
      net.sourceforge.czt.z.ast.ZName zpn = (net.sourceforge.czt.z.ast.ZName) proofName;
      // not null ==> empty
      if (zpn.getZStrokeList() == null || zpn.getZStrokeList().isEmpty()) {
	      return zpn;
	  }
    }
    final String message = "Expected the default (Z) implementation of Name with no strokes" +
      " but found " + String.valueOf(proofName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
