  /** Creates a parameterless call action. This is a convenience method */
  CallAction createCallAction(net.sourceforge.czt.z.ast.Name name);
  
  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  CallProcess createCallProcess(net.sourceforge.czt.z.ast.Name name);
  
  /** Creates an empty BasicNameSet. This is a convenience method */
  CircusNameSet createEmptyCircusNameSet();

  /** Creates an empty BasicChannelSet. This is a convenience method */
  CircusChannelSet createEmptyCircusChannelSet();
  
  /** 
   * Creates a CircusProcessSignature properly packing the last two signatures
   * within the rather complex AST structure underneath.
   */  
  CircusProcessSignature createCircusProcessSignature(
      net.sourceforge.czt.z.ast.Name name, 
      net.sourceforge.czt.z.ast.ZNameList genFormals,
      net.sourceforge.czt.z.ast.Signature paramOrIndexes,
      net.sourceforge.czt.z.ast.Signature usedChannels,
      ProcessKind kind);

  /** 
   * Follows the strategy from createCircusProcessSignature, but also considering
   * the last four extra elments involved in BasicProcessSignature.
   */  
  BasicProcessSignature createBasicProcessSignature(
      net.sourceforge.czt.z.ast.Name name, 
      net.sourceforge.czt.z.ast.ZNameList genFormals,
      net.sourceforge.czt.z.ast.Signature paramOrIndexes,
      net.sourceforge.czt.z.ast.Signature usedChannels,
      ProcessKind kind,
      net.sourceforge.czt.z.ast.Signature usedNameSets,
      net.sourceforge.czt.z.ast.Signature stateSignature,
      ZSignatureList localZParagraphs,
      ActionSignatureList processActions); 
