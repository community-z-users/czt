  /** Creates a parameterless call action. This is a convenience method */
  CallAction createCallAction(Name name);
  
  /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
  CallProcess createCallProcess(Name name);
  
  /** Creates an empty BasicNameSet. This is a convenience method */
  CircusNameSet createEmptyCircusNameSet();

  /** Creates an empty BasicChannelSet. This is a convenience method */
  CircusChannelSet createEmptyCircusChannelSet();
  
  /** Creates an interleave action with empty (basic) name sets. This is a convenience method */    
  InterleaveAction createInterleaveAction(CircusAction left, CircusAction right);
  
  
