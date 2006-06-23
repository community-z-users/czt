
    /** Creates a parameterless call action. This is a convenience method */
    public CallAction createCallAction(RefName name) {
      return createCallAction(name, createZExprList());
    }

    /** Creates a parameterless call process with empty generic actuals. This is a convenience method */
    public CallProcess createCallProcess(RefName name) {
      return createCallProcess(createRefExpr(name, createZExprList(), Boolean.FALSE, Boolean.TRUE), 
		createZExprList(), CallKind.Param);
    }
    
    /** Creates an empty BasicNameSet. This is a convenience method */
    public NameSet createEmptyNameSet() {
      return createNameSet(createSetExpr(createZExprList()));
    }
    
    /** Creates an empty BasicChannelSet. This is a convenience method */
    public ChannelSet createEmptyChannelSet() {
      return createChannelSet(createSetExpr(createZExprList()));
    }
    
    /** Creates an interleave action with empty (basic) name sets. This is a convenience method */    
    public InterleaveAction createInterleaveAction(CircusAction left, CircusAction right) {
      return createInterleaveAction(left, right, createEmptyNameSet(), createEmptyNameSet());
    }
