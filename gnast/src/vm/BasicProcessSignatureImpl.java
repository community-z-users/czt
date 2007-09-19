
  public net.sourceforge.czt.z.ast.Signature getUsedNameSets()
  {
    if (getMainSignatures().size() > 2) {
      return getMainSignatures().get(2);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public void setUsedNameSets(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > 2) {
      assert sig != null;
      getMainSignatures().set(2, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
  
  public net.sourceforge.czt.z.ast.Signature getStateSignature()
  {
    if (getMainSignatures().size() > 3) {
      return getMainSignatures().get(3);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
  
  public void setStateSignature(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > 3) {
      assert sig != null;
      getMainSignatures().set(3, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.circus.ast.ZSignatureList getLocalZSignatures()
  {
    if (getSignatureList().size() > 1) {
        net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(1);
        if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList) {
          return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
        }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures()
  {
    if (getSignatureList().size() > 2) {
        net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(2);
        if (sigList instanceof net.sourceforge.czt.circus.ast.ActionSignatureList) {
          return (net.sourceforge.czt.circus.ast.ActionSignatureList) sigList;
        }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

