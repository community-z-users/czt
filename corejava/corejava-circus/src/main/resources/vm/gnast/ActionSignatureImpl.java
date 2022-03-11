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

  public boolean isParamAction()
  {
    return (!getFormalParams().getNameTypePair().isEmpty());
  }

  public net.sourceforge.czt.circus.ast.ZSignatureList getZSignatureList()
  {
    net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList();
    if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList)
    {
      return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
    }
    final String message = "Expected the default (Circus) implementation of SignatureList" +
      " but found " + String.valueOf(sigList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature getFormalParams()
  {
    if (getZSignatureList().size() > FORMAL_PARAMS_INDEX)
    {
      return getZSignatureList().get(FORMAL_PARAMS_INDEX);
    }
    final String message = "Invalid action signature list size. Expected a value greater than " + 
        FORMAL_PARAMS_INDEX + " but found " + getZSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature setFormalParams(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > FORMAL_PARAMS_INDEX)
    {
      assert sig != null;
      return getZSignatureList().set(FORMAL_PARAMS_INDEX, sig);
    }
    final String message = "Invalid action signature list size. Expected a value greater than " + 
        FORMAL_PARAMS_INDEX + " but found " + getZSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature getLocalVars()
  {
    if (getZSignatureList().size() > LOCAL_VARS_INDEX)
    {
      return getZSignatureList().get(LOCAL_VARS_INDEX);
    }
    final String message = "Invalid action signature list size. Expected a value greater than " + 
        LOCAL_VARS_INDEX + " but found " + getZSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature setLocalVars(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > LOCAL_VARS_INDEX)
    {
      assert sig != null;
      return getZSignatureList().set(LOCAL_VARS_INDEX, sig);
    }
    final String message = "Invalid action signature list size. Expected a value greater than " + 
        LOCAL_VARS_INDEX + " but found " + getZSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature getUsedChannels()
  {
    if (getZSignatureList().size() > USED_CHANNELS_INDEX)
    {
      return getZSignatureList().get(USED_CHANNELS_INDEX);
    }
    final String message = "Invalid action signature list size. Expected a value greater than " + 
        USED_CHANNELS_INDEX + " but found " + getZSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature setUsedChannels(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getZSignatureList().size() > USED_CHANNELS_INDEX)
    {
      assert sig != null;
      return getZSignatureList().set(USED_CHANNELS_INDEX, sig);
    }
    final String message = "Invalid action signature list size. Expected a value greater than " + 
        USED_CHANNELS_INDEX + " but found " + getZSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.circus.ast.CircusCommunicationList getUsedCommunications()
  {
    return net.sourceforge.czt.circus.util.CircusUtils.assertCircusCommunicationList(getCommunicationList());
  }

  public net.sourceforge.czt.circus.ast.CircusChannelSetList getUsedChannelSets()
  {
    return net.sourceforge.czt.circus.util.CircusUtils.assertCircusChannelSetList(getChannelSetList());
  }

  public net.sourceforge.czt.circus.ast.CircusNameSetList getUsedNameSets()
  {
    return net.sourceforge.czt.circus.util.CircusUtils.assertCircusNameSetList(getNameSetList());
  }

