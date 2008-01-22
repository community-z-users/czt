
  public net.sourceforge.czt.z.ast.Name getActionName()
  {
    return getName();
  }
  
  public net.sourceforge.czt.z.ast.ZName getActionZName()
  {
    return getZName();
  }
  
  public void setActionName(net.sourceforge.czt.z.ast.Name name)
  {
    setName(name);
  }  

  public boolean isActionPara()
  {
    return (getName() != null);
  }

  public boolean isParamAction()
  {
    return (!getFormalParams().getNameTypePair().isEmpty());
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
    if (getZSignatureList().size() > FORMAL_PARAMS_INDEX ) {
      return getZSignatureList().get(FORMAL_PARAMS_INDEX );
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  } 
  
  public void setFormalParams(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > FORMAL_PARAMS_INDEX ) {
      assert sig != null;
      getZSignatureList().set(FORMAL_PARAMS_INDEX , sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }   

  public net.sourceforge.czt.z.ast.Signature getLocalVars()
  {
    if (getZSignatureList().size() > LOCAL_VARS_INDEX) {
      return getZSignatureList().get(LOCAL_VARS_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
  
  public void setLocalVars(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > LOCAL_VARS_INDEX) {
      assert sig != null;
      getZSignatureList().set(LOCAL_VARS_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }    
  
  public net.sourceforge.czt.z.ast.Signature getUsedNameSets()
  {
    if (getZSignatureList().size() > USED_NAMESETS_INDEX) {
      return getZSignatureList().get(USED_NAMESETS_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  } 
  
  public void setUsedNameSets(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > USED_NAMESETS_INDEX ) {
      assert sig != null;
      getZSignatureList().set(USED_NAMESETS_INDEX , sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }

  public net.sourceforge.czt.circus.ast.CircusCommunicationList getUsedCommunications()      
  {
    return net.sourceforge.czt.circus.util.CircusUtils.assertCircusCommunicationList(getCommunicationList());
  }
