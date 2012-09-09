
  public net.sourceforge.czt.z.ast.ZName getVariableZName()
  {
    net.sourceforge.czt.z.ast.Name declName = getVariableName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
