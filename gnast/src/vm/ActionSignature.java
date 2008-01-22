  static final int FORMAL_PARAMS_INDEX = 0;
  static final int LOCAL_VARS_INDEX    = 1;
  static final int USED_NAMESETS_INDEX = 2;

  /**
   * This is a convenience method for getName.
   */
  net.sourceforge.czt.z.ast.Name getActionName();

  /**
   * Returns whether or not this is a signature for Action or ActionPara
   * (i.e. it has a name or not associated with it).
   */   
  boolean isActionPara();  
  
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
   * a UnsupportedAstClassException from getMainSignatures().
   */  
  void setFormalParams(net.sourceforge.czt.z.ast.Signature sig);
 
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
   * a UnsupportedAstClassException from getMainSignatures().
   */    
  void setLocalVars(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of used name sets for this action signature (i.e. parallel actions).
   * It returns the Signature from getZSignatureList().get(USED_NAMESETS_INDEX). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getUsedNameSets();  
  
  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of used name sets for this action signature (i.e. parallel actions).
   * It is the same as getZSignatureList().set(USED_NAMESETS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */    
  void setUsedNameSets(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used channels within the communications of this action. This includes 
   * generic, implicit, or normal communications. It may throw a UnsupportedAstClassException 
   * from getCommunicationList().
   */
  net.sourceforge.czt.circus.ast.CircusCommunicationList getUsedCommunications();
