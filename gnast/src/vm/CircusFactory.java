  /** Creates a parameterless call action. This is a convenience method */
  CallAction createCallAction(RefName name);
  
  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  CallProcess createCallProcess(RefName name, CallType ctype);
  
  /** Creates an empty BasicNameSet. This is a convenience method */
  NameSet createEmptyNameSet();

  /** Creates an empty BasicChannelSet. This is a convenience method */
  ChannelSet createEmptyChannelSet();
  
  /** Creates an interleave action with empty (basic) name sets. This is a convenience method */    
  InterleaveAction createInterleaveAction(CircusAction left, CircusAction right);
  
  
  
