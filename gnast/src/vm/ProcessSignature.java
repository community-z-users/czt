  final static int FORMAL_PARAMS_INDEX   = 0;
  final static int STATE_SIGNATURE_INDEX = 1;

  final static int MAIN_SIGNATURES_INDEX    = 0;
  final static int PROCESS_SIGNATURES_INDEX = 1;
  final static int ACTION_SIGNATURES_INDEX  = 2;
  final static int LOCALZ_SIGNATURES_INDEX  = 3;
  
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
  net.sourceforge.czt.z.ast.Signature getFormalParamsOrIndexes();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the formal parameters or indexes signature of this process.
   * It is the same as getMainSignatures().set(FORMAL_PARAMS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setFormalParamsOrIndexes(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty, [ | true ])
   * signature of the process state. It returns the Signature from getMainSignatures().get(STATE_SIGNATURE_INDEX). 
   * It may throw a UnsupportedAstClassException from getMainSignatures().
   */
  net.sourceforge.czt.z.ast.Signature getStateSignature();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the state signature of this process.
   * It is the same as getMainSignatures().set(STATE_SIGNATURE_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   */
  net.sourceforge.czt.z.ast.Signature setStateSignature(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ProcessSignature objects only.
   * It returns the ProcessSignature if getSignatureList().get(PROCESS_SIGNATURES_INDEX) is an instance of
   * ProcessSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ProcessSignatureList getProcessSignatures();

  /**
   * Returns true whether or not this signature is for a basic process or not. 
   * That is, if the getProcessSignatures().isEmpty(). All auxiliary methods 
   * below with a Map result are always empty when isBasicProcessSignature() 
   * is not true. That is to say, only collect action signature information from
   * basic processes. 
   */
  boolean isBasicProcessSignature();

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ActionSignature objects only.
   * It returns the ActionSignatureList if getSignatureList().get(ACTION_SIGNATURES_INDEX) is an instance of
   * ActionSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures();

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ZSignatureList objects only.
   * It returns the ZSignatureList if getSignatureList().get(LOCALZ_SIGNATURES_INDEX) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getBasicProcessLocalZSignatures();
  
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of declared local paragraphs within a basic process or across multiple
   * basic processes. 
   * 
   * This method calculates on-the-fly the local paragraphs from all basic processes of this
   * process. If it is an basic process already, only one element is present. That is, for basic 
   * process this is just the process name mapped to its getBasicProcessLocalZSignatures(). 
   * For non-basic processes, it maps the process names to a ZSignature list of each constituent
   * process from getProcessSignatures() that is a basic process, and this is done recursively.
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList> getLocalZSignatures();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used communications within the prefixing actions of this process. This includes 
   * generic, implicit, or normal communications. 
   * 
   * This method calculates on-the-fly the communications from all actions of this
   * processes, if it is a basic process. It is empty otherwise. That is, it maps
   * action names to a list of name type pairs of channel names and their declared types,
   * and is calculated through getActionSignatures().
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.z.ast.Signature> getUsedChannels();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used communications within the prefixing actions of this process. This includes 
   * generic, implicit, or normal communications. 
   * 
   * This method calculates on-the-fly the communications from all actions of this
   * processes, if it is a basic process. It is empty otherwise. That is, it maps
   * action names to a list of communications, and is calculated through getActionSignatures().
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusCommunicationList> getUsedCommunications();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used channel sets within this process. 
   * 
   * This method calculates on-the-fly the channel sets from all actions of this
   * processes, if it is a basic process. It is empty otherwise. That is, it maps 
   * action names to a list of channel sets, and is calculated through getActionSignatures().
   * 
   * For parallel processes channel sets, one should look into getParallelProcessesChannelSets.
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusChannelSetList> getUsedChannelSets();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of used name sets within this process.  
   * 
   * This method calculates on-the-fly the name sets from all actions of this
   * processes, if it is a basic process. It is empty otherwise. That is, it maps
   * action names to a list of name sets, and is calculated through getActionSignatures().
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusNameSetList> getUsedNameSets();

