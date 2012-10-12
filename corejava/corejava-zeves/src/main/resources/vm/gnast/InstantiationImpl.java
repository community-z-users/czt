
  public net.sourceforge.czt.z.ast.ZName getZName()
  {
    net.sourceforge.czt.z.ast.Name instName = getName();
    if (instName instanceof net.sourceforge.czt.z.ast.ZName) {
      net.sourceforge.czt.z.ast.ZName zpn = (net.sourceforge.czt.z.ast.ZName) instName;
	  return zpn;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(instName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
