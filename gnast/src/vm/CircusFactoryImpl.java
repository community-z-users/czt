
    /** Creates a parameterless call action. This is a convenience method */
    public CallAction createCallAction(net.sourceforge.czt.z.ast.Name name) {
      return createCallAction(name, createZExprList());
    }

    /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
    public CallProcess createCallProcess(net.sourceforge.czt.z.ast.Name name) {
      return createCallProcess(createRefExpr(name, createZExprList(), Boolean.FALSE, Boolean.TRUE),
      createZExprList(), CallUsage.Param);
    }
    
    /** Creates an empty BasicNameSet. This is a convenience method */
    public CircusNameSet createEmptyCircusNameSet() {
      return createCircusNameSet(createSetExpr(createZExprList()));
    }
    
    /** Creates an empty BasicChannelSet. This is a convenience method */
    public CircusChannelSet createEmptyCircusChannelSet() {
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

  public ActionSignature createActionSignature(Name actionName, 
    Signature formals, Signature localVars, CommunicationList usedChannels)
  {    
    ActionSignature result = createActionSignature(
      actionName, 
      createZSignatureList(newList(formals, localVars)), 
      usedChannels);
    return result;    
  }
  
  public CircusProcessSignature createCircusProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.circus.ast.CommunicationList usedChannels,
    ProcessUsage usage)
  {
    return createCircusProcessSignature(name, genFormals,
      newList(
        // list0 = ZSignatureList getMainSignatures()
        createZSignatureList(
          // list0.0 = Signature paramOrIndexes
          newList(paramOrIndexes)
        )
      ),
      usedChannels,
      usage);
  }
  
  public BasicProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.circus.ast.CommunicationList usedChannels,
    ProcessUsage usage,
    net.sourceforge.czt.z.ast.Signature usedNameSets,
    net.sourceforge.czt.z.ast.ZNameList declTransformerPara,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ZSignatureList localZParagraphs,
    ActionSignatureList processActions,
    StateUpdate stateUpdate)
  {
    return createBasicProcessSignature(name, genFormals,
      newList(
        // list0 = ZSignatureList getMainSignatures()
        createZSignatureList(
          // list0.0 = Signature paramOrIndexes
          // list0.1 = Signature usedNameSets
          // list0.2 = Signature stateSignature
          newList(paramOrIndexes, usedNameSets, stateSignature)
        ),
        // list1 = ZSignatureList getLocalZSignatures()
        localZParagraphs,
        // list2 = ActionSignatureList getActionSignatures()
        processActions
      ),
      usedChannels,
      usage, 
      declTransformerPara,
      stateUpdate);
  }

  public BasicProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.circus.ast.CommunicationList usedChannels,
    ProcessUsage usage,
    net.sourceforge.czt.z.ast.Signature usedNameSets,
    net.sourceforge.czt.z.ast.ZNameList declTransformerPara,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ZSignatureList localZParagraphs,
    ActionSignatureList processActions)
  {
    return createBasicProcessSignature(name, genFormals,
      paramOrIndexes, usedChannels, usage, usedNameSets, 
      declTransformerPara, stateSignature, localZParagraphs, 
      processActions, createStateUpdate());
  }
  
  public ActionSignature createEmptyActionSignature()
  {
    // create an empty signature, but with the right place holders.
    ActionSignature result = createActionSignature(
      null,               // action name
      createSignature(),  // empty formal paramenters
      createSignature(),  // empty local variables
      createCircusCommunicationList() // empty communications
    );
    return result;   
  }
  
  public ProcessSignature createEmptyCircusProcessSignature()
  {
    // create an empty signature, but with the right place holders.
    ProcessSignature result = createCircusProcessSignature(
      null,                 // process name
      createZNameList(),    // generic types 
      createSignature(),    // param or indexes
      createCircusCommunicationList(),    // used channels
      ProcessUsage.Parameterised);
    return result;   
  }
  
  public BasicProcessSignature createEmptyBasicProcessSignature()
  {
    // create an empty signature, but with the right place holders.
    BasicProcessSignature result = createBasicProcessSignature(
      null,                     // process name
      createZNameList(),        // generic types 
      createSignature(),        // param or indexes
      createCircusCommunicationList(),        // used channels
      ProcessUsage.Parameterised,// parameter usage
      createSignature(),        // used name sets
      createZNameList(),        // declared transformer para
      createSignature(),        // state signature      
      createZSignatureList(),   // local z paragraphs signature list
      createActionSignatureList(), // action paragraphs signature list
      createStateUpdate());     // state update information
    return result;   
  }  
