  public net.sourceforge.czt.z.ast.ZNameList getZGenFormals()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getGenFormals();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(rnl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }


  public net.sourceforge.czt.z.ast.ZName getZName()
  {
    net.sourceforge.czt.z.ast.Name declName = getName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public boolean isBasicProcess()
  {
    return net.sourceforge.czt.circus.util.CircusUtils.isBasicProcess(getCircusProcess());
  }

  public net.sourceforge.czt.circus.ast.BasicProcess getCircusBasicProcess()
  {
    if (isBasicProcess())    
    {
      return net.sourceforge.czt.circus.util.CircusUtils.getBasicProcess(getCircusProcess());
    }
    final String message = "Expected BasicProcess element for ProcessPara " +
      " but found " + String.valueOf(getCircusProcess());
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
  
  public void setCircusBasicProcess(net.sourceforge.czt.circus.ast.BasicProcess term)
  {
    if (isBasicProcess())    
    {
      net.sourceforge.czt.circus.ast.CircusProcess process = getCircusProcess();
      // for basic process paragraphs, just update the circus process element
      if (process instanceof net.sourceforge.czt.circus.ast.BasicProcess)
        setCircusProcess(term);
      // for parameterised basic process, update the inner process of ProcessD
      else if (process instanceof net.sourceforge.czt.circus.ast.ProcessD)
        ((net.sourceforge.czt.circus.ast.ProcessD)process).setCircusProcess(term);
      // otherwise this is an error
      else
        throw new net.sourceforge.czt.base.util.UnsupportedAstClassException("Basic process paragraph has inner process that is neither BasicProcess nor ProcessD - " + process.getClass().getName());
    }
    else
    {
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException("Not basic process paragraph");
    }
  }
