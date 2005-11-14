  /** Creates a list of synchronisation channels. This is a convenience method */
  public ChannelDecl createSynchChannelDecl(java.util.List<? extends DeclName> chans);
  
  /** Creates a parameterless call action. This is a convenience method */
  public CallAction createCallAction(RefName name);
  
  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  public CallProcess createCallProcess(RefName name, CallType ctype);
  
  /** Creates an empty BasicNameSet. This is a convenience method */
  public NameSet createEmptyNameSet();

  /** Creates an empty BasicChannelSet. This is a convenience method */
  public ChannelSet createEmptyChannelSet();
  
  /** Creates an interleave action with empty (basic) name sets. This is a convenience method */    
  public InterleaveAction createInterleaveAction(CircusAction left, CircusAction right);
  
  
  
