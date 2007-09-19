
  /**
   * This is a convenience method.
   * It returns the ZName if getName is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZName getActionName();

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
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of locally declared variables for this action signature (i.e. circvar commands).
   * It returns the Signature from getZSignatureList().get(1). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getLocalVars();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of used channels within this action signature.
   * It returns the Signature from getZSignatureList().get(2). It may throw a
   * a UnsupportedAstClassException from getZSignatureList().
   */
  net.sourceforge.czt.z.ast.Signature getUsedChannels();      
