  /** Creates a parameterless call action. This is a convenience method */
  public CallAction createCallAction(net.sourceforge.czt.z.ast.Name name)
  {
    return createCallAction(name, createZExprList());
  }

  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  public CallProcess createCallProcess(net.sourceforge.czt.z.ast.Name name)
  {
    return createCallProcess(createRefExpr(name, createZExprList(),
      Boolean.FALSE, Boolean.TRUE),
      createZExprList(), CallUsage.Param);
  }

  /** Creates an empty BasicNameSet. This is a convenience method */
  public CircusNameSet createEmptyCircusNameSet()
  {
    return createCircusNameSet(createSetExpr(createZExprList()));
  }

  /** Creates an empty BasicChannelSet. This is a convenience method */
  public CircusChannelSet createEmptyCircusChannelSet()
  {
    return createCircusChannelSet(createSetExpr(createZExprList()));
  }

  private <E> java.util.List<E> newList(E... elems)
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }
  private final ZName synchNameWithoutID_ = createZName(
    net.sourceforge.czt.circus.util.CircusString.CIRCUSSYNCH,
    createZStrokeList(), null);

  public ZName createSynchName()
  {
    return synchNameWithoutID_;
  }

  public PowerType createSynchType()
  {
    PowerType result = createPowerType(createGivenType(createSynchName()));
    return result;
  }

  public DotField createOutputField(net.sourceforge.czt.z.ast.Expr e)
  {
    DotField result = createDotField(e);
    result.getAnns().add(createOutputFieldAnn());
    return result;
  }
  
  protected ActionSignature createCompleteActionSignature(
    net.sourceforge.czt.z.ast.Name actionName,
    net.sourceforge.czt.z.ast.Signature formals,
    net.sourceforge.czt.z.ast.Signature localVars,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    CommunicationList usedComms,
    ChannelSetList usedChannelSets,
    NameSetList usedNameSets, 
    boolean signatureOfMuAction)
  {
    ActionSignature result = createActionSignature(
      actionName,
      createZSignatureList(newList(formals, localVars, usedChannels)),
      usedComms, usedChannelSets, usedNameSets, signatureOfMuAction);
    return result;
  }

  public ActionSignature createEmptyActionSignature()
  {
    // create an empty signature, but with the right place holders.
    ActionSignature result = createCompleteActionSignature(
      null,                              // null action name
      createSignature(),                 // empty formal paramenters
      createSignature(),                 // empty local variables
      createSignature(),                 // empty channels
      createCircusCommunicationList(),   // empty communications
      createCircusChannelSetList(),      // empty channel sets 
      createCircusNameSetList(),         // empty name sets
      false                              // not for a MuAction
      );
    return result;
  }
  
  public ActionSignature createInitialMuActionSignature(net.sourceforge.czt.z.ast.Name actionName)
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
      createCircusNameSetList(),         // empty name sets
      true);
  }  

  public ActionSignature createActionSignature(
    net.sourceforge.czt.z.ast.Name actionName,
    net.sourceforge.czt.z.ast.Signature formals,
    net.sourceforge.czt.z.ast.Signature localVars,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    CommunicationList usedComms,
    ChannelSetList usedChannelSets,
    NameSetList usedNameSets)
  {
    return createCompleteActionSignature(actionName, formals, 
        localVars, usedChannels, usedComms, usedChannelSets, 
        usedNameSets, false);
  }

  protected ProcessSignature createCompleteProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ProcessSignatureList processSignatures,
    ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures,
    ChannelSetList parallelProcessChannelSets,
    StateUpdate stateUpdate,
    ProcessUsage usage)
  {
    return createProcessSignature(name, genFormals,
      newList(
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

  public ProcessSignature createEmptyProcessSignature()
  {
    return createCompleteProcessSignature(null, createZNameList(),
      createSignature(),
      createSignature(), createProcessSignatureList(),
      createActionSignatureList(), createZSignatureList(),
      createCircusChannelSetList(), createStateUpdate(),
      ProcessUsage.Parameterised);
  }

  public ProcessSignature createProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    ProcessSignatureList processSignatures,
    ProcessUsage usage)
  {
    return createCompleteProcessSignature(name, genFormals, paramOrIndexes,
      createSignature(), processSignatures, createActionSignatureList(),
      createZSignatureList(), createCircusChannelSetList(), 
      createStateUpdate(), usage);
  }

  public ProcessSignature createChannelSetProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    ProcessSignatureList processSignatures,
    ChannelSetList channelSets,
    ProcessUsage usage)
  {
    return createCompleteProcessSignature(name, genFormals, paramOrIndexes,
      createSignature(), processSignatures, createActionSignatureList(),
      createZSignatureList(), channelSets, createStateUpdate(), usage);
  }

  public ProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures,
    StateUpdate stateUpdate,
    ProcessUsage usage)
  {
    return createCompleteProcessSignature(name, genFormals, paramOrIndexes,
      stateSignature, createProcessSignatureList(), actionSignatures,
      basicProcessLocalZSignatures, createCircusChannelSetList(), stateUpdate, usage);
  }

  public ProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures,
    ProcessUsage usage)
  {
    return createBasicProcessSignature(name, genFormals, paramOrIndexes,
      stateSignature, actionSignatures, basicProcessLocalZSignatures, 
      createStateUpdate(), usage);
  }
