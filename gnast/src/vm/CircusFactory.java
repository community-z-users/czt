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
  ZName createSynchName();

  /**
   * Creates the synchronisation channel type. It creates a power type of a given type 
   * containing createSynchName() as the given type name.
   */
  PowerType createSynchType();
  
  ActionSignature createActionSignature(
    net.sourceforge.czt.z.ast.Name actionName, 
    net.sourceforge.czt.z.ast.Signature formals, 
    net.sourceforge.czt.z.ast.Signature localVars, 
    CommunicationList usedChannels);    

  /** 
   * Creates a CircusProcessSignature properly packing the last two signatures
   * within the rather complex AST structure underneath.
   */  
  CircusProcessSignature createCircusProcessSignature(
      net.sourceforge.czt.z.ast.Name name, 
      net.sourceforge.czt.z.ast.ZNameList genFormals,
      net.sourceforge.czt.z.ast.Signature paramOrIndexes,
      CommunicationList usedChannels,
      ProcessUsage usage);

  BasicProcessSignature createBasicProcessSignature(
    net.sourceforge.czt.z.ast.Name name,
    net.sourceforge.czt.z.ast.ZNameList genFormals,
    net.sourceforge.czt.z.ast.Signature paramOrIndexes,
    CommunicationList usedChannels,
    ProcessUsage usage,
    net.sourceforge.czt.z.ast.Signature usedNameSets,
    net.sourceforge.czt.z.ast.ZNameList declTransformerPara,    
    net.sourceforge.czt.z.ast.Signature stateSignature,
    ZSignatureList localZParagraphs,
    ActionSignatureList processActions,
    StateUpdate stateUpdate);

  /** 
   * Follows the strategy from createCircusProcessSignature, but also considering
   * the last four extra elments involved in BasicProcessSignature.
   */  
  BasicProcessSignature createBasicProcessSignature(
      net.sourceforge.czt.z.ast.Name name, 
      net.sourceforge.czt.z.ast.ZNameList genFormals,
      net.sourceforge.czt.z.ast.Signature paramOrIndexes,
      CommunicationList usedChannels,
      ProcessUsage usage,
      net.sourceforge.czt.z.ast.Signature usedNameSets,
      net.sourceforge.czt.z.ast.ZNameList declTransformerPara,
      net.sourceforge.czt.z.ast.Signature stateSignature,
      ZSignatureList localZParagraphs,
      ActionSignatureList processActions); 
  
  /**
   * Creates an empty action signature. That is, an action signature with null name,
   * empty communication list, empty local variables and formal parameters. Note that
   * The signature itself is not totally empty since getZSignatureList() returns a list
   * containing the two empty signatures for formal parameters and local variables.
   */
  ActionSignature createEmptyActionSignature();
  
  ProcessSignature createEmptyCircusProcessSignature();
  
  BasicProcessSignature createEmptyBasicProcessSignature();
