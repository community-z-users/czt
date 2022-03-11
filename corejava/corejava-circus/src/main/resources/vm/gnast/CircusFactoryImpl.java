  /** Creates a parameterless call action. This is a convenience method */
  public net.sourceforge.czt.circus.ast.CallAction createCallAction(net.sourceforge.czt.z.ast.Name name)
  {
    return createCallAction(name, createZExprList());
  }

  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  public net.sourceforge.czt.circus.ast.CallProcess createCallProcess(net.sourceforge.czt.z.ast.Name name)
  {
    return createCallProcess(createRefExpr(name, createZExprList(),
      Boolean.FALSE, Boolean.TRUE),
      createZExprList(), net.sourceforge.czt.circus.ast.CallUsage.Parameterised);
  }

  /** Creates an empty BasicNameSet. This is a convenience method */
  public net.sourceforge.czt.circus.ast.CircusNameSet createEmptyCircusNameSet()
  {
    return createCircusNameSet(createSetExpr(createZExprList()));
  }

  /** Creates an empty BasicChannelSet. This is a convenience method */
  public net.sourceforge.czt.circus.ast.CircusChannelSet createEmptyCircusChannelSet()
  {
    return createCircusChannelSet(createSetExpr(createZExprList()));
  }

  private <E> java.util.List<E> newList(@SuppressWarnings("unchecked") E... elems)
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }
  
  private final net.sourceforge.czt.z.ast.ZName synchNameWithoutID_ = createZName(
    net.sourceforge.czt.circus.util.CircusString.CIRCUSSYNCH,
    createZStrokeList(), null);

  public net.sourceforge.czt.z.ast.ZName createSynchName()
  {
    return synchNameWithoutID_;
  }

  public net.sourceforge.czt.z.ast.PowerType createSynchType()
  {
	  net.sourceforge.czt.z.ast.PowerType result = createPowerType(createGivenType(createSynchName()));
    return result;
  }

  public net.sourceforge.czt.circus.ast.DotField createOutputField(net.sourceforge.czt.z.ast.Expr e)
  {
	  net.sourceforge.czt.circus.ast.DotField result = createDotField(e);
    result.getAnns().add(createOutputFieldAnn());
    return result;
  }
  
  public net.sourceforge.czt.circus.ast.ActionSignature createCompleteActionSignature(
    net.sourceforge.czt.z.ast.Name actionName,
    net.sourceforge.czt.z.ast.Signature formals,
    net.sourceforge.czt.z.ast.Signature localVars,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    net.sourceforge.czt.circus.ast.CommunicationList usedComms,
    net.sourceforge.czt.circus.ast.ChannelSetList usedChannelSets,
    net.sourceforge.czt.circus.ast.NameSetList usedNameSets)
  {
	  net.sourceforge.czt.circus.ast.ActionSignature result = 
			  createActionSignature(actionName, 
					  createZSignatureList(newList(formals, localVars, usedChannels)),
					  	usedComms, usedChannelSets, usedNameSets);
    return result;
  }

  public net.sourceforge.czt.circus.ast.ActionSignature createEmptyActionSignature()
  {
    // create an empty signature, but with the right place holders.
	  net.sourceforge.czt.circus.ast.ActionSignature result = createCompleteActionSignature(
      null,                              // null action name
      createSignature(),                 // empty formal paramenters
      createSignature(),                 // empty local variables
      createSignature(),                 // empty channels
      createCircusCommunicationList(),   // empty communications
      createCircusChannelSetList(),      // empty channel sets 
      createCircusNameSetList()          // empty name sets
      );
    return result;
  }
  
  public net.sourceforge.czt.circus.ast.ActionSignature createInitialMuActionSignature(net.sourceforge.czt.z.ast.Name actionName)
  {
    if (actionName == null)
    {
        throw new IllegalArgumentException("Invalid (null) MuAction name");
    } 
    return createCompleteActionSignature(actionName,
      createSignature(),                 // empty formal paramenters
      createSignature(),                 // empty local variables
      createSignature(),                 // empty channels
      createCircusCommunicationList(),   // empty communications
      createCircusChannelSetList(),      // empty channel sets 
      createCircusNameSetList()          // empty name sets
      );
  }  

  public net.sourceforge.czt.circus.ast.ActionSignature createActionSignature(
    net.sourceforge.czt.z.ast.Name actionName,
    net.sourceforge.czt.z.ast.Signature formals,
    net.sourceforge.czt.z.ast.Signature localVars,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    net.sourceforge.czt.circus.ast.CommunicationList usedComms,
    net.sourceforge.czt.circus.ast.ChannelSetList usedChannelSets,
    net.sourceforge.czt.circus.ast.NameSetList usedNameSets)
  {
    return createCompleteActionSignature(actionName, formals, 
        localVars, usedChannels, usedComms, usedChannelSets, 
        usedNameSets);
  }

  public net.sourceforge.czt.circus.ast.ProcessSignature createCompleteProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    net.sourceforge.czt.circus.ast.ProcessSignatureList processSignatures,
    net.sourceforge.czt.circus.ast.ActionSignatureList actionSignatures,
    net.sourceforge.czt.circus.ast.ZSignatureList basicProcessLocalZSignatures,
    net.sourceforge.czt.circus.ast.ChannelSetList parallelProcessChannelSets,
    net.sourceforge.czt.circus.ast.StateUpdate stateUpdate,
    net.sourceforge.czt.circus.ast.CallUsage usage)
  {
    return createProcessSignature(name, genFormals,
   		this.<net.sourceforge.czt.circus.ast.SignatureList>newList(
        // list0 = ZSignatureList getMainSignatures()
        createZSignatureList(
          // list0.0 = Signature paramOrIndexes          
          // list0.1 = Signature stateSignature
          newList(paramOrIndexes, stateSignature)),
        // list1 = ProcessSignatureList getProcessSignatures()
        processSignatures,
        // list2 = ActionSignatureList getActionSignatures()
        actionSignatures,
        // list3 = ZSignatureList getBasicProcessLocalZSignatures()
        basicProcessLocalZSignatures
      ),
      parallelProcessChannelSets,
      stateUpdate,
      usage);
  }

  public net.sourceforge.czt.circus.ast.ProcessSignature createEmptyProcessSignature()
  {
    return createCompleteProcessSignature(null, createZNameList(),
      createSignature(),
      createSignature(), createProcessSignatureList(),
      createActionSignatureList(), createZSignatureList(),
      createCircusChannelSetList(), createStateUpdate(),
      net.sourceforge.czt.circus.ast.CallUsage.Parameterised);
  }

  public net.sourceforge.czt.circus.ast.ProcessSignature createProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.circus.ast.ProcessSignatureList processSignatures,
    net.sourceforge.czt.circus.ast.CallUsage usage)
  {
    return createCompleteProcessSignature(name, genFormals, paramOrIndexes,
      createSignature(), processSignatures, createActionSignatureList(),
      createZSignatureList(), createCircusChannelSetList(), 
      createStateUpdate(), usage);
  }

  public net.sourceforge.czt.circus.ast.ProcessSignature createChannelSetProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.circus.ast.ProcessSignatureList processSignatures,
    net.sourceforge.czt.circus.ast.ChannelSetList channelSets,
    net.sourceforge.czt.circus.ast.CallUsage usage)
  {
    return createCompleteProcessSignature(name, genFormals, paramOrIndexes,
      createSignature(), processSignatures, createActionSignatureList(),
      createZSignatureList(), channelSets, createStateUpdate(), usage);
  }

  public net.sourceforge.czt.circus.ast.ProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    net.sourceforge.czt.circus.ast.ActionSignatureList actionSignatures,
    net.sourceforge.czt.circus.ast.ZSignatureList basicProcessLocalZSignatures,
    net.sourceforge.czt.circus.ast.StateUpdate stateUpdate,
    net.sourceforge.czt.circus.ast.CallUsage usage)
  {
    return createCompleteProcessSignature(name, genFormals, paramOrIndexes,
      stateSignature, createProcessSignatureList(), actionSignatures,
      basicProcessLocalZSignatures, createCircusChannelSetList(), stateUpdate, usage);
  }

  public net.sourceforge.czt.circus.ast.ProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    net.sourceforge.czt.circus.ast.ActionSignatureList actionSignatures,
    net.sourceforge.czt.circus.ast.ZSignatureList basicProcessLocalZSignatures,
    net.sourceforge.czt.circus.ast.CallUsage usage)
  {
    return createBasicProcessSignature(name, genFormals, paramOrIndexes,
      stateSignature, actionSignatures, basicProcessLocalZSignatures, 
      createStateUpdate(), usage);
  }

