
  public net.sourceforge.czt.z.ast.ZName getActionName()
  {
    return getZName();
  }
  
  public net.sourceforge.czt.circus.ast.ZSignatureList getZSignatureList()
  {
    net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList();
    if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList) {
      return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature getFormalParams()
  {
    if (getZSignatureList().size() > 0) {
      return getZSignatureList().get(0);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
 
  public net.sourceforge.czt.z.ast.Signature getLocalVars()
  {
    if (getZSignatureList().size() > 1) {
      return getZSignatureList().get(1);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
  
  public net.sourceforge.czt.z.ast.Signature getUsedChannels()      
  {
    if (getZSignatureList().size() > 2) {
      return getZSignatureList().get(2);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
