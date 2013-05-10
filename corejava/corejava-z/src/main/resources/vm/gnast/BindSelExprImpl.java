
  public net.sourceforge.czt.z.ast.ZName getZName()
  {
	  net.sourceforge.czt.z.ast.Name refName = getName();
    if (refName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) refName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(refName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
