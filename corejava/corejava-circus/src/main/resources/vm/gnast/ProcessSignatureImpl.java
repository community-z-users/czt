  public net.sourceforge.czt.z.ast.Name getProcessName()
  {
    return getName();
  }

  public net.sourceforge.czt.z.ast.ZName getProcessZName()
  {
    assert getName() != null : "cannot cast null process name as ZName";
    return getZName();
  }

  public void setProcessName(net.sourceforge.czt.z.ast.Name name)
  {
    setName(name);
  }
    
  public net.sourceforge.czt.circus.ast.CircusChannelSetList getCircusProcessChannelSets()
  {
    // DESIGN: leave it as assertions - as these are pre conditions, we can assume them - don't raise errors
    // assert !isBasicProcessSignature() : "basic processes do not have process channels";
    net.sourceforge.czt.circus.ast.ChannelSetList channelSets = getProcessChannelSets();
    if (channelSets instanceof net.sourceforge.czt.circus.ast.CircusChannelSetList) {
      return (net.sourceforge.czt.circus.ast.CircusChannelSetList) channelSets;
    }
    final String message = "Expected the default (Circus) implementation of ChannelSetList" +
      " but found " + String.valueOf(channelSets);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
  
  public net.sourceforge.czt.circus.ast.ZSignatureList getMainSignatures()
  {
    if (getSignatureList().size() > MAIN_SIGNATURES_INDEX)
    {
      net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().get(MAIN_SIGNATURES_INDEX);
      if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList)
      {
        return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
      }
      final String message = "Expected the Circus implementation of local Z SignatureList" +
        " but found " + String.valueOf(sigList);
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
    }
    final String message = "Invalid process signature list size. Expected a value greater than " + 
        MAIN_SIGNATURES_INDEX + " for basic process signatures but found " + getSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature getFormalParamsOrIndexes()
  {    
    assert !isBasicProcessSignature() : "basic processes do not have formal parameters or indexes signature";
    if (getMainSignatures().size() > FORMAL_PARAMS_INDEX)
    {
      return getMainSignatures().get(FORMAL_PARAMS_INDEX);
    }
    final String message = "Invalid top-level process signature list size. Expected a value greater than " + 
        FORMAL_PARAMS_INDEX + " for fomal paramters but found " + getMainSignatures().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature setFormalParamsOrIndexes(net.sourceforge.czt.z.ast.Signature sig)
  {
    assert !isBasicProcessSignature() : "basic processes do not have formal parameters or indexes signature";
    if (getMainSignatures().size() > FORMAL_PARAMS_INDEX)
    {
      assert sig != null;
      getMainSignatures().set(FORMAL_PARAMS_INDEX, sig);
    }
    final String message = "Invalid top-lvel process signature list size. Expected a value greater than " + 
        FORMAL_PARAMS_INDEX + " for fomal paramters but found " + getMainSignatures().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature getStateSignature()
  {
    assert isBasicProcessSignature() : "non basic processes do not have local state signature";
    if (getMainSignatures().size() > STATE_SIGNATURE_INDEX)
    {
      return getMainSignatures().get(STATE_SIGNATURE_INDEX);
    }
    final String message = "Invalid basic process signature main signature list size. Expected a value greater than " + 
        STATE_SIGNATURE_INDEX + " for process state signature but found " + getMainSignatures().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.Signature setStateSignature(net.sourceforge.czt.z.ast.Signature sig)
  {
    assert isBasicProcessSignature() : "non basic processes do not have local state signature";
    if (getMainSignatures().size() > STATE_SIGNATURE_INDEX)
    {
      assert sig != null;
      return getMainSignatures().set(STATE_SIGNATURE_INDEX, sig);
    }
    final String message = "Invalid basic process signature main signature list size. Expected a value greater than " + 
        STATE_SIGNATURE_INDEX + " for process state signature but found " + getMainSignatures().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
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
      final String message = "Expected the implementation of Process SignatureList" +
        " but found " + String.valueOf(sigList);
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
    }
    final String message = "Invalid top-level process signature list size. Expected a value greater than " + 
        PROCESS_SIGNATURES_INDEX + " for inner process signatures but found " + getSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public boolean isBasicProcessSignature()
  {
    return getProcessSignatures().isEmpty() && getCircusProcessChannelSets().isEmpty();
  }  
  
  public boolean isEmptyProcessSignature()
  {
    return isBasicProcessSignature() && getStateSignature().getNameTypePair().isEmpty() &&
      getBasicProcessLocalZSignatures().isEmpty() && getActionSignatures().isEmpty() 
      //&& getGenFormals().isEmpty() && getProcessName() == null
      ;
  }
  
  public net.sourceforge.czt.circus.ast.ZSignatureList getBasicProcessLocalZSignatures()
  {
    assert isBasicProcessSignature() : "non basic processes do not have list of local Z signatures";
    if (getSignatureList().size() > LOCALZ_SIGNATURES_INDEX)
    {
      net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().
        get(LOCALZ_SIGNATURES_INDEX);
      if (sigList instanceof net.sourceforge.czt.circus.ast.ZSignatureList)
      {
        return (net.sourceforge.czt.circus.ast.ZSignatureList) sigList;
      }
      final String message = "Expected the implementation of local Z SignatureList" +
        " but found " + String.valueOf(sigList);
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
    }
    final String message = "Invalid basic process signature list size. Expected a value greater than " + 
        LOCALZ_SIGNATURES_INDEX + " for local z signature but found " + getMainSignatures().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures()
  {
    assert isBasicProcessSignature() : "non basic processes do not have list of local action signatures";
    if (getSignatureList().size() > ACTION_SIGNATURES_INDEX)
    {
      net.sourceforge.czt.circus.ast.SignatureList sigList = getSignatureList().
        get(ACTION_SIGNATURES_INDEX);
      if (sigList instanceof net.sourceforge.czt.circus.ast.ActionSignatureList)
      {
        return (net.sourceforge.czt.circus.ast.ActionSignatureList) sigList;
      }
      final String message = "Expected the implementation of local Action SignatureList" +
        " but found " + String.valueOf(sigList);
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);

    }
    final String message = "Invalid basic process signature list size. Expected a value greater than " + 
        ACTION_SIGNATURES_INDEX + " for actions signature but found " + getSignatureList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
  
  /**
   * Add the given key/value pair to the given map, raising an error in case of duplicates.
   * @param map
   * @param key
   * @param value
   */
  protected <K, V> void addToMapAndCheckConsistency(java.util.Map<K,V> map, K key, V value)
  {
    assert !map.containsKey(key) : "Illegal value for " + getProcessName() + ". " + "The key " + key + " already had a previous value assigned.";
    V old = map.put(key, value);
    if (old != null)      
      throw new net.sourceforge.czt.util.CztException("Illegal value for " + getProcessName() + ". " + 
        "The key " + key + " already had a previous value assigned.");
  }
  
  /**
   * For a process P and action A, their fully qualified name is "P_LxCy.A",
   * where x and y are the line and column numbers from LocAnn associated with P.
   * @param procName
   * @param actionName
   * @return
   */
  protected net.sourceforge.czt.z.ast.ZName fullQualifiedName(net.sourceforge.czt.z.ast.ZName procName, net.sourceforge.czt.z.ast.ZName actionName)
  {    
    return net.sourceforge.czt.circus.util.CircusUtils.qualifyName(procName, actionName);
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList> getLocalZSignatures()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList>();
    // for basic processes this is just one entry 
    if (isBasicProcessSignature())
    {      
      addToMapAndCheckConsistency(result, getProcessZName(), getBasicProcessLocalZSignatures());
    }
    // for other processes this includes all entries of all of its inner basic processes.
    else
    {      
      for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
      {
        for(java.util.Map.Entry<net.sourceforge.czt.z.ast.ZName, 
            net.sourceforge.czt.circus.ast.ZSignatureList> entry : pSig.getLocalZSignatures().entrySet())
        {          
          // for local Z names, the map is between process name and entry values
          addToMapAndCheckConsistency(result, entry.getKey(), entry.getValue());
        }                  
      }
    }
    return result;
  }

  public java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ActionSignatureList> getActions()
  {
    java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ActionSignatureList> result = new java.util.HashMap<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ActionSignatureList>();
    // for basic processes this is just one entry 
    if (isBasicProcessSignature())
    {      
      addToMapAndCheckConsistency(result, getProcessZName(), getActionSignatures());
    }
    // for other processes this includes all entries of all of its inner basic processes.
    else
    {      
      for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
      {
        for(java.util.Map.Entry<net.sourceforge.czt.z.ast.ZName, 
            net.sourceforge.czt.circus.ast.ActionSignatureList> entry : pSig.getActions().entrySet())
        {          
          // for local Z names, the map is between process name and entry values
          addToMapAndCheckConsistency(result, entry.getKey(), entry.getValue());
        }                  
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
        addToMapAndCheckConsistency(result, aSig.getActionZName(), aSig.getUsedChannels());
      }
    }
    // for other processes this includes all entries of all of its inner basic processes.
    else
    {
      net.sourceforge.czt.z.ast.ZName procName;
      if (getProcessName() == null) 
      {
        //assert !getFormalParamsOrIndexes().getNameTypePair().isEmpty() : "unamed non-basic process must be parameterised(?)";
        procName = net.sourceforge.czt.circus.util.CircusUtils.createAnonymousZName();
      }
      else
      {
        procName = getProcessZName();
      }
      for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
      {
        for(java.util.Map.Entry<net.sourceforge.czt.z.ast.ZName, 
            net.sourceforge.czt.z.ast.Signature> entry : pSig.getUsedChannels().entrySet())
        {
          // to avoid name clash, fully qualify the process name with the action name.
          net.sourceforge.czt.z.ast.ZName newKey = fullQualifiedName(procName, entry.getKey());
          addToMapAndCheckConsistency(result, newKey, entry.getValue());          
        }                  
      }
    }
    return result;
  }
  
  public java.util.List<net.sourceforge.czt.z.ast.NameTypePair> getUsedChannelsAsList()
  {    
    java.util.List<net.sourceforge.czt.z.ast.NameTypePair> result = new java.util.ArrayList<net.sourceforge.czt.z.ast.NameTypePair>();
    for(net.sourceforge.czt.z.ast.Signature sig : getUsedChannels().values())
    {
      for(net.sourceforge.czt.z.ast.NameTypePair ntp : sig.getNameTypePair())
      {
        if (!result.contains(ntp)) result.add(ntp);
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
    // for other processes this includes all entries of all of its inner basic processes.
    else
    {
      net.sourceforge.czt.z.ast.ZName procName;
      if (getProcessName() == null) 
      {
        //assert !getFormalParamsOrIndexes().getNameTypePair().isEmpty() : "unamed non-basic process must be parameterised(?)";
        procName = net.sourceforge.czt.circus.util.CircusUtils.createAnonymousZName();
      }
      else
      {
        procName = getProcessZName();
      }
      for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
      {
        for(java.util.Map.Entry<net.sourceforge.czt.z.ast.ZName, 
            net.sourceforge.czt.circus.ast.CircusCommunicationList> entry : pSig.getUsedCommunications().entrySet())
        {
          // to avoid name clash, fully qualify the process name with the action name.
          net.sourceforge.czt.z.ast.ZName newKey = fullQualifiedName(procName, entry.getKey());
          addToMapAndCheckConsistency(result, newKey, entry.getValue());          
        }                  
      }
    }
    return result;
  }
  
  public java.util.List<net.sourceforge.czt.circus.ast.Communication> getUsedCommunicationsAsList()
  {    
    java.util.List<net.sourceforge.czt.circus.ast.Communication> result = new java.util.ArrayList<net.sourceforge.czt.circus.ast.Communication>();
    for(net.sourceforge.czt.circus.ast.CircusCommunicationList comms : getUsedCommunications().values())
    {
      for(net.sourceforge.czt.circus.ast.Communication comm : comms)
      {
        if (!result.contains(comm)) result.add(comm);
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
    // for other processes this includes all entries of all of its inner basic processes.
    else
    {
      net.sourceforge.czt.z.ast.ZName procName;
      if (getProcessName() == null) 
      {
        //assert !getFormalParamsOrIndexes().getNameTypePair().isEmpty() : "unamed non-basic process must be parameterised(?)";
        procName = net.sourceforge.czt.circus.util.CircusUtils.createAnonymousZName();
      }
      else
      {
        procName = getProcessZName();
      }
      for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
      {
        for(java.util.Map.Entry<net.sourceforge.czt.z.ast.ZName, 
            net.sourceforge.czt.circus.ast.CircusChannelSetList> entry : pSig.getUsedChannelSets().entrySet())
        {
          // to avoid name clash, fully qualify the process name with the action name.
          net.sourceforge.czt.z.ast.ZName newKey = fullQualifiedName(procName, entry.getKey());
          addToMapAndCheckConsistency(result, newKey, entry.getValue());          
        }                  
      }
    }
    return result;
  }
  
  public java.util.List<net.sourceforge.czt.circus.ast.ChannelSet> getUsedChannelSetsAsList()
  {    
    java.util.List<net.sourceforge.czt.circus.ast.ChannelSet> result = new java.util.ArrayList<net.sourceforge.czt.circus.ast.ChannelSet>();
    for(net.sourceforge.czt.circus.ast.CircusChannelSetList chansets : getUsedChannelSets().values())
    {
      for(net.sourceforge.czt.circus.ast.ChannelSet cs : chansets)
      {
        if (!result.contains(cs)) result.add(cs);
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
    // for other processes this includes all entries of all of its inner basic processes.
    else
    {
      net.sourceforge.czt.z.ast.ZName procName;
      if (getProcessName() == null) 
      {
        //assert !getFormalParamsOrIndexes().getNameTypePair().isEmpty() : "unamed non-basic process must be parameterised(?)";
        procName = net.sourceforge.czt.circus.util.CircusUtils.createAnonymousZName();
      }
      else
      {
        procName = getProcessZName();
      }
      for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
      {
        for(java.util.Map.Entry<net.sourceforge.czt.z.ast.ZName, 
            net.sourceforge.czt.circus.ast.CircusNameSetList> entry : pSig.getUsedNameSets().entrySet())
        {
          // to avoid name clash, fully qualify the process name with the action name.
          net.sourceforge.czt.z.ast.ZName newKey = fullQualifiedName(procName, entry.getKey());
          addToMapAndCheckConsistency(result, newKey, entry.getValue());          
        }                  
      }
    }
    return result;
  }
  
  public java.util.List<net.sourceforge.czt.circus.ast.NameSet> getUsedNameSetsAsList()
  {    
    java.util.List<net.sourceforge.czt.circus.ast.NameSet> result = new java.util.ArrayList<net.sourceforge.czt.circus.ast.NameSet>();
    for(net.sourceforge.czt.circus.ast.CircusNameSetList namesets : getUsedNameSets().values())
    {
      for(net.sourceforge.czt.circus.ast.NameSet ns : namesets)
      {
        if (!result.contains(ns)) result.add(ns);
      }
    }
    return result;
  }  

