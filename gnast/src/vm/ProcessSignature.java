
  /**
   * This is a convenience method.
   * It returns the ZName if ProcessName is an instance of
	   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZName getProcessName();

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing Z Signature objects only. 
   * It returns the ZSignatureList if getSignatureList().get(0) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getMainSignatures();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of param or indexes of a process. The difference is given by the getKind() method.  
   * It returns the Signature from getMainSignatures().get(0). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getParamOrIndexes();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of used channels by this process. This (possibly) includes channels used 
   * by its actions, in case it is a BasicProcessSignature.
   * It returns the Signature from getMainSignatures().get(1). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getUsedChannels();
