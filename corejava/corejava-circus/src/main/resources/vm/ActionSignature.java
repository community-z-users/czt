  final static int FORMAL_PARAMS_INDEX = 0;
  final static int LOCAL_VARS_INDEX    = 1;
  final static int USED_CHANNELS_INDEX = 2;

  /**
   * This is a convenience method for getName.
   */
  net.sourceforge.czt.z.ast.Name getActionName();
  
  /**
   * Returns whether or not this is a signature for parameterised action or not
   * (i.e. it has a non-empty list of formal parameters).
   */
  boolean isParamAction();

  /**
   * This is a convenience method.
   * It returns the ZName if getName is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZName getActionZName();

  /**
   * This is a convenience method for setName.
   */
  void setActionName(net.sourceforge.czt.z.ast.Name name);

  /**
   * This is a convenience method.
   * It returns the ZSignatureList if getSignatureList() is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getZSignatureList();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of arguments for this action signature (i.e. its declared formal parameters).
   * It returns the Signature from getZSignatureList().get(FORMAL_PARAMS_INDEX). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().     
   */
  net.sourceforge.czt.z.ast.Signature getFormalParams();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the formal parameters signature of this action.
   * It is the same as getZSignatureList().set(FORMAL_PARAMS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setFormalParams(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of locally declared variables for this action signature (i.e. circvar commands).
   * It returns the Signature from getZSignatureList().get(LOCAL_VARS_INDEX). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getLocalVars();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the local variables signature of this action.
   * It is the same as getZSignatureList().set(LOCAL_VARS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setLocalVars(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of used channels for this action signature. This contains the channel
   * name and its declared type
   * It returns the Signature from getZSignatureList().get(USED_CHANNELS_INDEX). 
   * It may throw a a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getUsedChannels();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of used channels for this action signature. This contains the channel
   * name and its declared type
   * It is the same as getZSignatureList().set(USED_CHANNELS_INDEX, sig). The result is 
   * the old value previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setUsedChannels(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used channels within the communications of this action. This includes 
   * generic, implicit, or normal communications. It may throw a UnsupportedAstClassException 
   * from getCommunicationList().
   */
  net.sourceforge.czt.circus.ast.CircusCommunicationList getUsedCommunications();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used name sets within the name sets of this action. 
   * It may throw a UnsupportedAstClassException from getNameSetListList().
   */
  net.sourceforge.czt.circus.ast.CircusNameSetList getUsedNameSets();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used channel sets within the name sets of this action. 
   * It may throw a UnsupportedAstClassException from getChannelSetListList().
   */
  net.sourceforge.czt.circus.ast.CircusChannelSetList getUsedChannelSets();
