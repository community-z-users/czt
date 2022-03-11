  public boolean isBasicProcess()
  {
    return (getCircusProcess() instanceof net.sourceforge.czt.circus.ast.BasicProcess);
  }

  public net.sourceforge.czt.circus.ast.BasicProcess getCircusBasicProcess()
  {
    net.sourceforge.czt.circus.ast.CircusProcess result = getCircusProcess();
    if (result instanceof net.sourceforge.czt.circus.ast.BasicProcess)
    {
      return (net.sourceforge.czt.circus.ast.BasicProcess)result;
    }
    final String message = "Expected the BasicProcess element for ProcessD " +
      " but found " + String.valueOf(result);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
