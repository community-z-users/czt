
  public net.sourceforge.czt.z.ast.Name getProcessName()
  {
    return getName();
  }
  
  public net.sourceforge.czt.z.ast.ZName getProcessZName()
  {
    return getZName();
  }
  
  public void setProcessName(net.sourceforge.czt.z.ast.Name name)
  {
    setName(name);
  }
  
  public boolean isProcessPara()
  {
    return (getName() != null);
  }
  
  public net.sourceforge.czt.circus.ast.ZSignatureList getMainSignatures()
  {
    if (getSignatureList().size() > MAIN_SIGNATURES_INDEX) {
        net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(MAIN_SIGNATURES_INDEX);
        if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList) {
          return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
        }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature getFormalParamsOrIndexes()
  {
    if (getMainSignatures().size() > FORMAL_PARAMS_INDEX) {
      return getMainSignatures().get(FORMAL_PARAMS_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.z.ast.Signature setFormalParamsOrIndexes(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > FORMAL_PARAMS_INDEX) {
      assert sig != null;
      getMainSignatures().set(FORMAL_PARAMS_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.z.ast.Signature getUsedChannels()
  {
    if (getMainSignatures().size() > USED_CHANNELS_INDEX) {
      return getMainSignatures().get(USED_CHANNELS_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.z.ast.Signature setUsedChannels(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > USED_CHANNELS_INDEX) {
      assert sig != null;
      getMainSignatures().set(USED_CHANNELS_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
    public net.sourceforge.czt.circus.ast.CircusCommunicationList getUsedCommunications()      
  {
    return net.sourceforge.czt.circus.util.CircusUtils.assertCircusCommunicationList(getCommunicationList());
  }
