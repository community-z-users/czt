  static final int FORMAL_PARAMS_INDEX = 0;

  static final int MAIN_SIGNATURES_INDEX = 0;

  /**
   * This is a convenience method for getName.
   */
  net.sourceforge.czt.z.ast.Name getProcessName();

  /**
   * This is a convenience method.
   * It returns the ZName if ProcessName is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZName getProcessZName();
  
  /**
   * This is a convenience method for setName.
   */  
  void setProcessName(net.sourceforge.czt.z.ast.Name name);  

  /**
   * Returns whether or not this is a signature for Process or ProcessPara
   * (i.e. it has a name or not associated with it).
   */   
  boolean isProcessPara();  

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing Z Signature objects only. 
   * It returns the ZSignatureList if getSignatureList().get(MAIN_SIGNATURES_INDEX) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getMainSignatures();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of param or indexes of a process. The difference is given by the getUsage() method.  
   * It returns the Signature from getMainSignatures().get(FORMAL_PARAMS_INDEX). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getParamOrIndexes();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the formal parameters or indexes signature of this process.
   * It is the same as getMainSignatures().set(FORMAL_PARAMS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  void setParamOrIndexes(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used channels within the communications of this action. This includes 
   * generic, implicit, or normal communications. It may throw a UnsupportedAstClassException 
   * from getCommunicationList().
   */
  net.sourceforge.czt.circus.ast.CircusCommunicationList getUsedCommunications();

