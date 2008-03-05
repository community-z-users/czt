
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
    if (getSignatureList().size() > MAIN_SIGNATURES_INDEX)
    {
      net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().
        get(MAIN_SIGNATURES_INDEX);
      if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList)
      {
        return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
      }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature getFormalParamsOrIndexes()
  {
    if (getMainSignatures().size() > FORMAL_PARAMS_INDEX)
    {
      return getMainSignatures().get(FORMAL_PARAMS_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature setFormalParamsOrIndexes(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > FORMAL_PARAMS_INDEX)
    {
      assert sig != null;
      getMainSignatures().set(FORMAL_PARAMS_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature getStateSignature()
  {
    if (getMainSignatures().size() > STATE_SIGNATURE_INDEX)
    {
      return getMainSignatures().get(STATE_SIGNATURE_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.z.ast.Signature setStateSignature(net.sourceforge.czt.z.ast.Signature sig)
  {
    if (getMainSignatures().size() > STATE_SIGNATURE_INDEX)
    {
      assert sig != null;
      return getMainSignatures().set(STATE_SIGNATURE_INDEX, sig);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public net.sourceforge.czt.circus.ast.ProcessSignatureList getProcessSignatures()
  {
    if (getSignatureList().size() > PROCESS_SIGNATURES_INDEX)
    {
      net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().
        get(PROCESS_SIGNATURES_INDEX);
      if (sigList instanceof net.sourceforge.czt.circus.ast.ProcessSignatureList)
      {
        return (net.sourceforge.czt.circus.ast.ProcessSignatureList) sigList;
      }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public boolean isBasicProcessSignature()
  {
    return getProcessSignatures().isEmpty();
  }

  public net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures()
  {
    if (getSignatureList().size() > ACTION_SIGNATURES_INDEX)
    {
      net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().
        get(ACTION_SIGNATURES_INDEX);
      if (sigList instanceof net.sourceforge.czt.circus.ast.ActionSignatureList)
      {
        return (net.sourceforge.czt.circus.ast.ActionSignatureList) sigList;
      }
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList> getLocalZSignatures()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList>();
    // only collect local signatures of basic processes
    if (isBasicProcessSignature())
    {
      for (net.sourceforge.czt.circus.ast.ActionSignature aSig : getActionSignatures())
      {
        result.put(aSig.getActionZName(), aSig.getZSignatureList());
      }
    }
    return result;
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.z.ast.Signature> getUsedChannels()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.z.ast.Signature> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.z.ast.Signature>();
    // only collect local signatures of basic processes
    if (isBasicProcessSignature())
    {
      for (net.sourceforge.czt.circus.ast.ActionSignature aSig : getActionSignatures())
      {
        result.put(aSig.getActionZName(), aSig.getUsedChannels());
      }
    }
    return result;
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusCommunicationList> getUsedCommunications()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusCommunicationList> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusCommunicationList>();
    // only collect local signatures of basic processes
    if (isBasicProcessSignature())
    {
      for (net.sourceforge.czt.circus.ast.ActionSignature aSig : getActionSignatures())
      {
        result.put(aSig.getActionZName(), aSig.getUsedCommunications());
      }
    }
    return result;
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusChannelSetList> getUsedChannelSets()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusChannelSetList> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusChannelSetList>();

    // only collect local signatures of basic processes
    if (isBasicProcessSignature())
    {
      for (net.sourceforge.czt.circus.ast.ActionSignature aSig : getActionSignatures())
      {
        result.put(aSig.getActionZName(), aSig.getUsedChannelSets());
      }
    }
    return result;
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusNameSetList> getUsedNameSets()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusNameSetList> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusNameSetList>();
    // only collect local signatures of basic processes
    if (isBasicProcessSignature())
    {
      for (net.sourceforge.czt.circus.ast.ActionSignature aSig : getActionSignatures())
      {
        result.put(aSig.getActionZName(), aSig.getUsedNameSets());
      }
    }
    return result;
  }
