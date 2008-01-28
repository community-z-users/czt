  static final int USED_NAMESETS_INDEX   = FORMAL_PARAMS_INDEX+1;
  static final int STATE_SIGNATURE_INDEX = FORMAL_PARAMS_INDEX+2;
  
  static final int ZLOCAL_SIGNATURES_INDEX = MAIN_SIGNATURES_INDEX+1;
  static final int ACTION_SIGNATURES_INDEX = MAIN_SIGNATURES_INDEX+2;  

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of the name sets used by this basic process.
   * It returns the Signature from getMainSignatures().get(USED_NAMESETS_INDEX). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getUsedNameSets();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the name sets used by this basic process.
   * It is the same as getMainSignatures().set(USED_NAMESETS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setUsedNameSets(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty, [ | true ])
   * signature of the basic process state. 
   * It returns the Signature from getMainSignatures().get(STATE_SIGNATURE_INDEX). It may throw a
   * a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getStateSignature();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the state signature of this basic process.
   * It is the same as getMainSignatures().set(STATE_SIGNATURE_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setStateSignature(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing Z Signature objects only.
   * It returns the ZSignatureList if getSignatureList().get(ZLOCAL_SIGNATURES_INDEX) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getLocalZSignatures();

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ActionSignature objects only.
   * It returns the ActionSignatureList if getSignatureList().get(ACTION_SIGNATURES_INDEX) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures();
