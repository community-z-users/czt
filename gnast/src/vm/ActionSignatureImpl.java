
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
  
  public void setFormalParams(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > 0) {
      assert sig != null;
      getZSignatureList().set(0, sig);
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
  
  public void setLocalVars(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > 1) {
      assert sig != null;
      getZSignatureList().set(1, sig);
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
  
  public void setUsedChannels(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > 2) {
      assert sig != null;
      getZSignatureList().set(2, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(); 
  }
  
  public boolean isActionPara()
  {
    return (getName() != null);
  }
