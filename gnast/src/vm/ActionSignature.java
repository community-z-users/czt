  /**
   * This is a convenience method for getName.
   */
  net.sourceforge.czt.z.ast.Name getActionName();

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
   * It returns the Signature from getZSignatureList().get(0). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().     
   */
  net.sourceforge.czt.z.ast.Signature getFormalParams();
  
  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the formal parameters signature of this action.
   * It is the same as getZSignatureList().set(0, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */  
  void setFormalParams(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of locally declared variables for this action signature (i.e. circvar commands).
   * It returns the Signature from getZSignatureList().get(1). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getLocalVars();  
  
  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the local variables signature of this action.
   * It is the same as getZSignatureList().set(1, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */    
  void setLocalVars(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of used channels within this action signature.
   * It returns the Signature from getZSignatureList().get(2). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getUsedChannels();      
  
  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the used channels signature of this action.
   * It is the same as getZSignatureList().set(2, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */  
  void setUsedChannels(net.sourceforge.czt.z.ast.Signature sig);
 
  /**
   * Returns whether or not this is a signature for Action or ActionPara
   * (i.e. it has a name or not associated with it). TODO: CHECK: relevance... 
   */   
  boolean isActionPara();  
