  /** Creates a parameterless call action. This is a convenience method */
  CallAction createCallAction(net.sourceforge.czt.z.ast.Name name);

  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  CallProcess createCallProcess(net.sourceforge.czt.z.ast.Name name);

  /** Creates an empty BasicNameSet. This is a convenience method */
  CircusNameSet createEmptyCircusNameSet();

  /** Creates an empty BasicChannelSet. This is a convenience method */
  CircusChannelSet createEmptyCircusChannelSet();

  /**
   * Creates the synchronisation channel name. This creates a ZName without strokes or ID
   * and with CircusString.CIRCUSSYNCH string as the name.
   */
  net.sourceforge.czt.z.ast.ZName createSynchName();

  /**
   * Creates the synchronisation channel type. It creates a power type of a given type 
   * containing createSynchName() as the given type name.
   */
  net.sourceforge.czt.z.ast.PowerType createSynchType();

  /**
   * Convenience method that creates a DotField and annotates it with an OutputFieldAnn
   */
  DotField createOutputField(net.sourceforge.czt.z.ast.Expr e);

  ActionSignature createCompleteActionSignature(
    net.sourceforge.czt.z.ast.Name actionName,
    net.sourceforge.czt.z.ast.Signature formals,
    net.sourceforge.czt.z.ast.Signature localVars,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    CommunicationList usedComms,
    ChannelSetList usedChannelSets,
    NameSetList usedNameSets);
    
  /**
   * Creates an empty action signature. That is, an action signature with null name,
   * empty communication, channel set and name set lists; as well as empty local variables 
   * and formal parameters and used channels signature. The MuAction signature flag is off.
   * Note that the signature itself is not totally empty since getZSignatureList() returns a list
   * containing the two empty signatures for formal parameters and local variables.
   */
  ActionSignature createEmptyActionSignature();
  
  /**
   * The initial action signature for a MuAction just contain its name. That is, it is
   * an empty action signature with the given name and the MuAction signature flag on.
   * Also, it requires that the given name is not null. It throws an IllegalArgumentException if it is. 
   */
  ActionSignature createInitialMuActionSignature(net.sourceforge.czt.z.ast.Name actionName);

  /**
   * Convenience method that adds the signatures passed to the SignatureList for
   * the main ActionSignature constructor. The MuAction signature flag is off.
   */
  ActionSignature createActionSignature(
    net.sourceforge.czt.z.ast.Name actionName,
    net.sourceforge.czt.z.ast.Signature formals,
    net.sourceforge.czt.z.ast.Signature localVars,
    net.sourceforge.czt.z.ast.Signature usedChannels,
    CommunicationList usedComms,
    ChannelSetList usedChannelSets,
    NameSetList usedNameSets);

 ProcessSignature createCompleteProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ProcessSignatureList processSignatures,
    ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures,
    ChannelSetList parallelProcessChannelSets,
    StateUpdate stateUpdate,
    CallUsage usage);
  
  /**
   * Creates an empty process signature. That is, an process signature with null name,
   * empty generic formals, empty formal parameters or indexes, empty list of 
   * process signatures, empty list of action signatures, empty list of process 
   * channel sets, empty state update, and Parameterised as default usage.
   */
  ProcessSignature createEmptyProcessSignature();

  /** 
   * Creates a ProcessSignature properly packing the various parameters
   * within the rather complex AST structure underneath. This is useful
   * for a general process (i.e. extenal choice or call process).
   */
  ProcessSignature createProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    ProcessSignatureList processSignatures,
    CallUsage usage);

  /** 
   * Creates a ProcessSignature properly packing the various parameters
   * within the rather complex AST structure underneath. This is useful
   * for a parallel or hiding processes, which contain channel sets explicitly.
   */
  ProcessSignature createChannelSetProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    ProcessSignatureList processSignatures,
    ChannelSetList channelSets,
    CallUsage usage);

  /** 
   * Creates a ProcessSignature properly packing the various parameters
   * within the rather complex AST structure underneath. This is useful
   * for a basic processes with state update information, like those with
   * assignment commands or schema expression actions.
   */
  ProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures,
    StateUpdate stateUpdate,
    CallUsage usage);

  /** 
   * Creates a ProcessSignature properly packing the various parameters
   * within the rather complex AST structure underneath. This is useful
   * for a basic processes in general. An empty state update information 
   * is added (i.e., nothing from the stateSignature goes into it!).
   */
  ProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures,
    CallUsage usage);

