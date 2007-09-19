  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of the name sets used by this basic process.
   * It returns the Signature from getMainSignatures().get(2). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getUsedNameSets();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the name sets used by this basic process.
   * It is the same as getMainSignatures().set(2, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  void setUsedNameSets(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty, [ | true ])
   * signature of the basic process state. 
   * It returns the Signature from getMainSignatures().get(3). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getStateSignature();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the state signature of this basic process.
   * It is the same as getMainSignatures().set(3, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  void setStateSignature(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing Z Signature objects only.
   * It returns the ZSignatureList if getSignatureList().get(1) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getLocalZSignatures();

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ActionSignature objects only.
   * It returns the ActionSignatureList if getSignatureList().get(2) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures();


