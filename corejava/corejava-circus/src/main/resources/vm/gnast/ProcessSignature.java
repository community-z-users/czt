  /*
   * NOTE:
   * although ProcessSignatureImpl is rather complex, we took the trouble to do it because many 
   * developers of Circus tools do not fully understand the language (e.g., undergrad and MSc.
   * students) to grasp all its nuances. This ProcessSignature implementation tries to shed 
   * as much light as possible in the complexities of Circus structures. 
   * (update after revision 6696[07/Mar/08], done 08/Mar/08) 
   */

  /****************************************
  /* Indexes used by access methods below *
   ****************************************/
  
  final static int FORMAL_PARAMS_INDEX   = 0;
  final static int STATE_SIGNATURE_INDEX = 1;

  final static int MAIN_SIGNATURES_INDEX    = 0;
  final static int PROCESS_SIGNATURES_INDEX = 1;
  final static int ACTION_SIGNATURES_INDEX  = 2;
  final static int LOCALZ_SIGNATURES_INDEX  = 3;
  
  /**************************
  /* Special access methods *
   **************************/
  
  /**
   * This is a convenience method for getName.
   * 
   * @return getName()
   */
  net.sourceforge.czt.z.ast.Name getProcessName();

  /**
   * This is a convenience method.
   * It returns the ZName if getName() is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   * 
   * PRE: (getName() instanceof ZName)
   * 
   * @return (ZName)getName()
   */
  net.sourceforge.czt.z.ast.ZName getProcessZName();

  /**
   * This is a convenience method for setName(name).
   * 
   * @param name the process name
   */
  void setProcessName(net.sourceforge.czt.z.ast.Name name);

  /**
   * This is a convenience method. It represents the list of used channel sets by
   * non-basic processes, such as parallel and hiding processes. Basic processes 
   * always return an empty list. isBasicProcessSignature() is not part of the 
   * precondition to simplify the type checking rules for these processes and 
   * avoid a chicken-and-egg problem.
   * It returns the CircusChannelSetList if getProcessChannelSets() is an instance of
   * CircusChannelSetList and throws an UnsupportedAstClassException otherwise.
   * 
   * PRE: (getProcessChannelSets() instanceof CircusChannelSetList)
   * 
   * @return (CircusChannelSetList)getProcessChannelSets()
   */
  CircusChannelSetList getCircusProcessChannelSets();  
  
  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing Z Signature objects only. 
   * It returns the ZSignatureList if getSignatureList().get(MAIN_SIGNATURES_INDEX) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   * 
   * PRE: getSignatureList().size() > MAIN_SIGNATURES_INDEX &&
   *      getSignatureList().get(MAIN_SIGNATURES_INDEX) instanceof ZSignatureList
   * 
   * @return (ZSignatureList)getSignatureList().get(MAIN_SIGNATURES_INDEX)
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getMainSignatures();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * signature of parameters or indexes of a process. The difference is given by the getUsage() method.  
   * It returns the Signature from getMainSignatures().get(FORMAL_PARAMS_INDEX). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). Parameterised basic processes 
   * are represented by a process signature with formal parameters and the basic process
   * signature within getProcessSignatures();
   * 
   * PRE: !isBasicProcessSignature() && getMainSignatures().size() > FORMAL_PARAMS_INDEX 
   * 
   * @return getMainSignatures().get(FORMAL_PARAMS_INDEX);
   */
  net.sourceforge.czt.z.ast.Signature getFormalParamsOrIndexes();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the formal parameters or indexes signature of this process.
   * It is the same as getMainSignatures().set(FORMAL_PARAMS_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   * 
   * PRE: sig != null && !isBasicProcessSignature() && getMainSignatures().size() > FORMAL_PARAMS_INDEX 
   * 
   * @param sig new non-null (possibly empty) state signature
   * @return getMainSignatures().set(FORMAL_PARAMS_INDEX, sig)
   */
  net.sourceforge.czt.z.ast.Signature setFormalParamsOrIndexes(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It represents the non-null (possibly empty, [ | true ])
   * signature of the basic process state. It returns the Signature from getMainSignatures().get(STATE_SIGNATURE_INDEX). 
   * It may throw a UnsupportedAstClassException from getMainSignatures(). Only basic processes can call this method
   * 
   * PRE: isBasicProcessSignature() && (getMainSignatures().size() > STATE_SIGNATURE_INDEX)
   * 
   * @return getMainSignatures().get(STATE_SIGNATURE_INDEX)
   */
  net.sourceforge.czt.z.ast.Signature getStateSignature();

  /**
   * This is a convenience method. It sets the given non-null (possibly empty)  
   * signature of the state signature of this basic process.
   * It is the same as getMainSignatures().set(STATE_SIGNATURE_INDEX, sig). It may throw a
   * a UnsupportedAstClassException from getMainSignatures(). The result is the old value 
   * previously stored (if any).
   * 
   * PRE: sig != null && isBasicProcessSignature() && (getMainSignatures().size() > STATE_SIGNATURE_INDEX)
   * 
   * @param sig new non-null (possibly empty) state signature
   * @return getMainSignatures().set(STATE_SIGNATURE_INDEX, sig)
   */
  net.sourceforge.czt.z.ast.Signature setStateSignature(net.sourceforge.czt.z.ast.Signature sig);

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ProcessSignature objects only. It represents the signatures of inner processes
   * of compound processes. So, it determines if a  process is basic or not.
   * It returns the ProcessSignature if getSignatureList().get(PROCESS_SIGNATURES_INDEX) is an instance of
   * ProcessSignatureList and throws a UnsupportedAstClassException otherwise.
   * 
   * PRE: (getSignatureList().size() > PROCESS_SIGNATURES_INDEX) &&
   *      (getSignatureList().get(PROCESS_SIGNATURES_INDEX) instanceof ProcessSignatureList)
   * 
   * @return (ProcessSignatureList)getSignatureList().get(PROCESS_SIGNATURES_INDEX)
   */
  net.sourceforge.czt.circus.ast.ProcessSignatureList getProcessSignatures();

  /**
   * Returns true whether or not this signature is for a basic process or not. 
   * That is, if both the inner process signatures and process channel set lists are empty.
   * All auxiliary methods below with a Map result are always empty when isBasicProcessSignature() 
   * is not true. That is to say, only collect action signature information from
   * basic processes. 
   * 
   * @return getProcessSignatures().isEmpty() && getCircusProcessChannelSets().isEmpty();
   */
  boolean isBasicProcessSignature();
  
  /**
   * Returns true whether or not this signature is empty. That is, all elements
   * are empty, and only process name and its generics are ignores on this check.
   * 
   * @return
   */  
  boolean isEmptyProcessSignature();

  /**
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ZSignatureList objects only. It can only be called for basic processes, 
   * and it represents the local Z paragraph signatures within a basic process. It also contains
   * locally declared predicate transformers.
   * It returns the ZSignatureList if getSignatureList().get(LOCALZ_SIGNATURES_INDEX) is an instance of
   * ZSignatureList and throws a UnsupportedAstClassException otherwise.
   * 
   * PRE: isBasicProcessSignature() && (getSignatureList().size() > LOCALZ_SIGNATURES_INDEX) &&
   *      (getSignatureList().get(LOCALZ_SIGNATURES_INDEX) instanceof ZSignatureList) 
   * 
   * @return (ZSignatureList)getSignatureList().get(LOCALZ_SIGNATURES_INDEX)
   * 
   */
  net.sourceforge.czt.circus.ast.ZSignatureList getBasicProcessLocalZSignatures();
  
  /**  
   * This is a convenience method. It extract from the list of signature lists the
   * one containing ActionSignature objects only. It can only be called for basic processes, and
   * it represents the action signatures within a basic process.
   * It returns the ActionSignatureList if getSignatureList().get(ACTION_SIGNATURES_INDEX) is an instance of
   * ActionSignatureList and throws a UnsupportedAstClassException otherwise.
   * 
   * PRE: isBasicProcessSignature() && (getSignatureList().size() > ACTION_SIGNATURES_INDEX) &&
   *      (getSignatureList().get(ACTION_SIGNATURES_INDEX) instanceof ActionSignatureList) 
   * 
   * @return (ActionSignatureList)getSignatureList().get(ACTION_SIGNATURES_INDEX)
   */
  net.sourceforge.czt.circus.ast.ActionSignatureList getActionSignatures();

  /*****************************
  /* Special recursive methods *
   *****************************/
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of declared local paragraphs within a basic process or across multiple
   * basic processes that are part of a compound process. 
   * 
   * This method calculates on-the-fly the local paragraphs from all basic processes of this
   * process. If it is an basic process already, only mapping is present. That is, for basic 
   * process this is just the process name mapped to its getBasicProcessLocalZSignatures(). 
   * For non-basic processes, it maps the process names to a ZSignatureList of each constituent
   * process from getProcessSignatures() that is a basic process, and this is done recursively.
   * 
   * A likely implementation could do something as the code below
   * <code>
   * java.util.Map result = new java.util.HashMap();
   * if (isBasicProcessSignature())
   * { 
   *   assert !result.containsKey(getProcessZName());
   *   result.put(getProcessZName(), getBasicProcessLocalZSignatures());
   * }     
   * else
   * {      
   *    for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
   *   {
   *     for(java.util.Map.Entry entry : pSig.getLocalZSignatures().entrySet())
   *     {             
   *       assert !result.containsKey(entry.getKey());
   *       result.put(entry.getKey(), entry.getValue());
   *     }                  
   *   }
   *  }
   *  return result;
   * </code>
   * 
   * The getActions() method have a similar pattern but access getActionSignatures() within the ProcessSignature instance
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ZSignatureList> getLocalZSignatures();
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of declared actions within a basic process or across multiple
   * basic processes that are part of a compound process. 
   * 
   * This method calculates on-the-fly the local paragraphs from all basic processes of this
   * process. If it is an basic process already, only mapping is present. That is, for basic 
   * process this is just the process name mapped to its getActionSignatures(). 
   * For non-basic processes, it maps the process names to a ActionSignatureList of each constituent
   * process from getProcessSignatures() that is a basic process, and this is done recursively.
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.ActionSignatureList> getActions();
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of channel declarations used within this process signature. 
   * 
   * This method calculates on-the-fly the channels used within all basic process of this
   * processes, if it is a basic process. That is, it maps action name to the signature containing
   * all pairs of channel name to their declared type within this action. It is calculated through 
   * getActionSignatures().getUsedChannels() for each action. 
   * 
   * For compound processes, all signatures from getProcessSignatures() are scanned for getUsedChannels()
   * and added to the resulting map. As different processes may repeat action names, we qualify the map
   * key with the process name. For instance, for a process P and action A, the mapping will have a key
   * "P_LxCy.A", where x and y represent line an column numbers where P is declared in the spec. source.
   * This is just additional information to the user and is non-mandatory, since process names cannot
   * be repeated within a section (and all its parents - i.e., Z global scope).
   * 
   * A likely implementation could do something as the code below
   * <code>
   * java.util.Map result = new java.util.HashMap();
   * if (isBasicProcessSignature())
   * {
   *   for (net.sourceforge.czt.circus.ast.ActionSignature aSig : getActionSignatures())
   *   {
   *     assert !result.containsKey(aSig.getActionZName());
   *     result.put(aSig.getActionZName(), aSig.getUsedChannels());
   *   }
   * }
   * else
   * {
   *   net.sourceforge.czt.z.ast.ZName procName = getProcessZName();
   *   for (net.sourceforge.czt.circus.ast.ProcessSignature pSig : getProcessSignatures())
   *   {
   *     for(java.util.Map.Entry entry : pSig.getUsedChannels().entrySet())
   *     {
   *       net.sourceforge.czt.z.ast.ZName newKey = fullQualifiedName(procName, entry.getKey());
   *       assert !result.containsKey(newKey);
   *       result.put(newKey, entry.getValue());
   *     }                  
   *   }
   * }
   * return result;
   * </code>
   * The remaining methods have a similar pattern but access different (corresponding) lists 
   * within getActionSignatures() for all ProcessSignature instances in getProcessSignatures().
   *
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.z.ast.Signature> getUsedChannels();

  java.util.List<net.sourceforge.czt.z.ast.NameTypePair> getUsedChannelsAsList();
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of communications used (without repetition) within this process signature. 
   * Note that typechecked communications will have type information annotated to them.
   * 
   * Typechecked communication will have a communication type annotation. This includes 
   * the channel name with its resolved type (it differs from the declared type if the 
   * channel is generic), and it also includes the resolved types for the communication
   * fields. These may be different from the declared channel type. 
   * ex: "c: \nat \cross \nat" and "c?x!0" "x \in \nat", which is one dimension of the channel type.
   * 
   * This method calculates on-the-fly the channel sets used within all basic process of this
   * processes, if it is a basic process. That is, it maps action name to a list containing
   * all communications used within this action (without repetition). It is calculated through 
   * getActionSignatures().getUsedCommunications() for each action. 
   * 
   * For compound processes, all signatures from getProcessSignatures() are scanned for getUsedCommunications()
   * and added to the resulting map. As different processes may repeat action names, we qualify the map
   * key with the process name. 
   * 
   * For instance, for a process P and action A, the mapping will have a key "P_LxCy.A", where x and y 
   * represent line an column numbers where P is declared in the spec. source.
   * This is just additional information to the user and is non-mandatory, since process names cannot
   * be repeated within a section (and all its parents - i.e., Z global scope).
   */   
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusCommunicationList> getUsedCommunications();
  
  java.util.List<net.sourceforge.czt.circus.ast.Communication> getUsedCommunicationsAsList();
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of channel sets used (without repetition) within this process signature. 
   * Note that typechecked channel sets will have type information annotated to them.
   * 
   * This method calculates on-the-fly the channel sets used within all basic process of this
   * processes, if it is a basic process. That is, it maps action name to a list containing
   * all channel sets used within this action (without repetition). It is calculated through 
   * getActionSignatures().getUsedChannelSets() for each action. 
   * 
   * For compound processes, all signatures from getProcessSignatures() are scanned for getUsedChannels()
   * and added to the resulting map. As different processes may repeat action names, we qualify the map
   * key with the process name. Note that compound process (i.e. parallel and hiding processes)
   * channel sets ARE NOT present in this map. This map contains only channel sets from basic processes
   * within the compound process AST.
   * 
   * For instance, for a process P and action A, the mapping will have a key "P_LxCy.A", where x and y 
   * represent line an column numbers where P is declared in the spec. source.
   * This is just additional information to the user and is non-mandatory, since process names cannot
   * be repeated within a section (and all its parents - i.e., Z global scope).
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusChannelSetList> getUsedChannelSets();

  java.util.List<net.sourceforge.czt.circus.ast.ChannelSet> getUsedChannelSetsAsList();
  
  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of name sets used (without repetition) within this process signature. 
   * Note that typechecked channel sets will have type information annotated to them.
   * 
   * This method calculates on-the-fly the channel sets used within all basic process of this
   * processes, if it is a basic process. That is, it maps action name to a list containing
   * all name sets used within this action (without repetition). It is calculated through 
   * getActionSignatures().getUsedNameSets() for each action. 
   * 
   * For compound processes, all signatures from getProcessSignatures() are scanned for getUsedNameSets()
   * and added to the resulting map. As different processes may repeat action names, we qualify the map
   * key with the process name. 
   * 
   * For instance, for a process P and action A, the mapping will have a key "P_LxCy.A", where x and y 
   * represent line an column numbers where P is declared in the spec. source.
   * This is just additional information to the user and is non-mandatory, since process names cannot
   * be repeated within a section (and all its parents - i.e., Z global scope).
   */
  java.util.Map<net.sourceforge.czt.z.ast.ZName, net.sourceforge.czt.circus.ast.CircusNameSetList> getUsedNameSets();
  
  java.util.List<net.sourceforge.czt.circus.ast.NameSet> getUsedNameSetsAsList();

