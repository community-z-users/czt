
  public net.sourceforge.czt.z.ast.Signature getUsedNameSets()
  {
    if (getMainSignatures().size() > USED_NAMESETS_INDEX) {
      return getMainSignatures().get(USED_NAMESETS_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.z.ast.Signature setUsedNameSets(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > USED_NAMESETS_INDEX) {
      assert sig != null;
      return getMainSignatures().set(USED_NAMESETS_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
  
  public net.sourceforge.czt.z.ast.Signature getStateSignature()
  {
    if (getMainSignatures().size() > STATE_SIGNATURE_INDEX) {
      return getMainSignatures().get(STATE_SIGNATURE_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
  
  public net.sourceforge.czt.z.ast.Signature setStateSignature(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > STATE_SIGNATURE_INDEX) {
      assert sig != null;
      return getMainSignatures().set(STATE_SIGNATURE_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.circus.ast.ZSignatureList getLocalZSignatures()
  {
    if (getSignatureList().size() > ZLOCAL_SIGNATURES_INDEX) {
        net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(ZLOCAL_SIGNATURES_INDEX);
        if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList) {
          return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
        }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures()
  {
    if (getSignatureList().size() > ACTION_SIGNATURES_INDEX) {
        net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(ACTION_SIGNATURES_INDEX);
        if (sigList instanceof net.sourceforge.czt.circus.ast.ActionSignatureList) {
          return (net.sourceforge.czt.circus.ast.ActionSignatureList) sigList;
        }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
