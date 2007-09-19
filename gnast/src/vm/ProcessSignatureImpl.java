
  public net.sourceforge.czt.z.ast.ZName getProcessName()
  {
    return getZName();
  }

  public net.sourceforge.czt.circus.ast.ZSignatureList getMainSignatures()
  {
    if (getSignatureList().size() > 0) {
        net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(0);
        if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList) {
          return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
        }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature getParamOrIndexes()
  {
    if (getMainSignatures().size() > 0) {
      return getMainSignatures().get(0);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.z.ast.Signature getUsedChannels()
  {
    if (getMainSignatures().size() > 1) {
      return getMainSignatures().get(1);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
