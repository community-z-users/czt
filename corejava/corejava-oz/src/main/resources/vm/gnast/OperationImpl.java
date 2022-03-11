
  public net.sourceforge.czt.z.ast.ZName getZName()
  {
	  net.sourceforge.czt.z.ast.Name name = getName();
    if (name instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) name;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(name);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

